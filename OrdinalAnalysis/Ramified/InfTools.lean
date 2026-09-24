/-
  Infinitary tools for `OmegaDerivableR`: structural combinators, ∀-inversion,
  and the passage from a finitary theorem to a uniform-height derivation of all
  its numeral instances.

  Three groups of facts, all generic in the height type `O`.

  * **Structural combinators.**  `weakening` and `exchange` restate the
    context-monotonicity already built into `OmegaDerivableR.contraction` in the
    shape later arguments want it (a subset inclusion, or a permutation).
    `cutR` packages a cut at the canonical height `max α β ⊕ 1` above both
    premises, and `omegaRuleUniform` packages the ω-rule for a *uniform* family
    of premise heights (one bound `β` for every instance, rather than a
    dependent family `β n`).  `existsInstR` is the analogous packaging on the
    ∃-side: a single witness at height `β` gives `∃¹ φ` at any `α` above `β`.
    `mono_lits` (monotonicity in the literal set) is already in
    `Ramified/Calculus.lean`; nothing is added for it here.

  * **∀-inversion**, `OmegaDerivableR.invAll`: from `⊢^α_ρ (∀¹ φ) :: Γ`, derive
    `⊢^α_ρ I.inst φ n :: Γ` for every `n`, at the *same* height and the *same*
    rank.  `Ramified/Reduction.lean` has no such lemma (its dispatcher inlines
    the one instance the reduction lemma needs), so this is a port of the
    classical inversion lemma for ω-rule calculi (Schütte; Pohlers), not of a
    finitary eigenvariable argument — the ω-rule already supplies exactly the
    instances, and the work is to show that whichever rule *actually* produced
    the ∀-formula in a given derivation, the same height still derives every
    instance in its place.

    The lemma is proved in the more general `⊆`-form `invAllSub`: if
    `Θ ⊆ (∀¹ φ) :: Γ` is derivable at height `α`, then so is `I.inst φ n :: Γ`,
    for every `n`, at the same `α`.  This is what the induction actually needs:
    at each rule the side formulas of `Θ` other than the occurrence of `∀¹ φ`
    being inverted are folded into `Γ` (via `⊆`, using `contraction` — genuine
    weakening — in *both* directions along the way: enlarging a premise's
    sequent to carry `∀¹ φ`'s witness alongside it, and afterwards dropping a
    duplicate or a side formula that is already accounted for in `Γ`).  Six of
    the eleven rules are dismissed by a head-tag mismatch with `∀¹`
    (`Ramified/Reduction.lean`'s `headTag`); `atom` is dismissed because an
    axiom is never a universal formula (`Literals.ne_all`); `contraction` needs
    only transitivity of `⊆`; `cut`, `or`, `and`, `pr`, `npr`, `exs` reconstruct
    the rule around the inverted premises and then drop the (now redundant)
    original side formula; `omegaRule` is the one genuine case split, on
    whether the occurrence being inverted is *this* rule's own principal
    formula (reflexive, closed by reusing the very premise the rule already
    supplies) or a different one buried in its context (reconstruct-and-drop,
    as for `or`/`and`).

    The generalised descent argument that motivates this file never needs the
    ∃ quantifier directly (the (Pr) rules and the ω-rule already cover every
    quantifier the ramified syntax produces); the ∃-side counterpart supplied
    here is the introduction combinator `existsInstR`, together with
    `weakening` and `exchange`, which are exactly what is needed to move a
    witness derivation into the shape the `exs` rule wants.

  * **Finitary theorem to uniform-height numeral instances**,
    `uniformHeight_of_provable_all_of` (generic in the theory `T`) and its
    `RAlt ν` corollary `uniformHeight_of_provable_all`: if `T ⊢! ∀¹ φ` (a
    universally quantified sentence), then there is a *single* height `α` with
    `⊢^α_ρ [evR ((emb φ)/[num n])]` for every `n`.  This is
    `Ramified/LowerBound.lean`'s replay-and-cut chain (`provable_omegaDerivable_of`
    or its `RAlt` specialisation `provable_omegaDerivable`), which already
    produces one uniform-height derivation of the whole sentence `∀¹ φ`, composed
    with `invAll`; the only new ingredient is `embAll`, commuting Foundation's
    sentence embedding with `∀¹` (`Rewriting.app_all` + `Rew.q_emb`, exactly as
    `Gentzen/AxiomsLogic.lean`'s `emb_relExtX` already does for a doubly
    quantified sentence).  A uniform bound on the embedded finitary heights
    needs exactly this: one derivation of a universally closed lemma, plus
    ∀-inversion, to feed a family of numeral instances at a common height into
    a further application of the ω-rule.
-/
import OrdinalAnalysis.Ramified.LowerBound
import OrdinalAnalysis.Ramified.Reduction

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Derivation

namespace OmegaDerivableR

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals LRA} {I : InstantiationR} {ρ : Gamma0Note}

/-! ### Structural combinators -/

/-- **Weakening.**  `contraction`, under the usual name: a bigger context, at
the same height. -/
theorem weakening {α : O} {Γ Δ : Sequent LRA} (hsub : Γ ⊆ Δ)
    (h : OmegaDerivableR A I ρ α Γ) : OmegaDerivableR A I ρ α Δ :=
  .contraction hsub h

/-- **Exchange.**  A permutation of a derivable sequent is derivable, at the
same height: `contraction` in the direction the permutation supplies. -/
theorem exchange {α : O} {Γ Δ : Sequent LRA} (hperm : List.Perm Γ Δ)
    (h : OmegaDerivableR A I ρ α Γ) : OmegaDerivableR A I ρ α Δ :=
  weakening hperm.subset h

/-- **A height-accounted cut combinator.**  The canonical height above two
premises, `max α β ⊕ 1` (`OrdinalNotation.lt_nadd_one` supplies the room on
each side), packaged so a caller need not exhibit the bound `γ` of `cut`
itself. -/
theorem cutR {α β : O} {φ : Proposition LRA} {Γ Δ : Sequent LRA} (hrk : rank φ < ρ)
    (h1 : OmegaDerivableR A I ρ α (φ :: Γ)) (h2 : OmegaDerivableR A I ρ β (∼φ :: Δ)) :
    OmegaDerivableR A I ρ (OrdinalNotation.nadd (max α β) OrdinalNotation.one) (Γ ++ Δ) :=
  .cut hrk (lt_of_le_of_lt (le_max_left α β) (OrdinalNotation.lt_nadd_one _))
    (lt_of_le_of_lt (le_max_right α β) (OrdinalNotation.lt_nadd_one _)) h1 h2

/-- **An ω-rule combinator at a uniform height.**  A single bound `β` for every
instance, rather than a dependent family, matching the way
`uniformHeight_of_provable_all_of` below produces its premises. -/
theorem omegaRuleUniform {β α : O} (hβ : β < α) {φ : Semiproposition LRA 1} {Γ : Sequent LRA}
    (h : ∀ n : ℕ, OmegaDerivableR A I ρ β (I.inst φ n :: Γ)) :
    OmegaDerivableR A I ρ α ((∀¹ φ) :: Γ) :=
  .omegaRule (fun _ => β) (fun _ => hβ) h

/-- **The ∃-side instance combinator.**  `exs`, with the height and the witness
reordered for readability; the ∃-side counterpart `omegaRuleUniform` needs
nothing beyond this and `weakening`/`exchange`. -/
theorem existsInstR {β α : O} (hβ : β < α) (n : ℕ) {φ : Semiproposition LRA 1} {Γ : Sequent LRA}
    (h : OmegaDerivableR A I ρ β (I.inst φ n :: Γ)) :
    OmegaDerivableR A I ρ α ((∃¹ φ) :: Γ) :=
  .exs n hβ h

/-! ### ∀-inversion -/

/-- **∀-inversion, `⊆`-form.**  If a sequent containing `Θ`'s formulas, together
with `∀¹ χ`, is derivable at height `α`, so is `Ξ` with `χ`'s `n`-th instance
adjoined, at the very same `α`.  See the module docstring for the case-by-case
argument; `invAll` below is the front-position corollary. -/
theorem invAllSub {α : O} {Θ : Sequent LRA} (h : OmegaDerivableR A I ρ α Θ) :
    ∀ {χ : Semiproposition LRA 1} {Ξ : Sequent LRA}, Θ ⊆ (∀¹ χ) :: Ξ →
      ∀ n : ℕ, OmegaDerivableR A I ρ α (I.inst χ n :: Ξ) := by
  induction h with
  | @atom α φ hAT =>
      intro χ Ξ hsub n
      have hhead : φ ∈ (∀¹ χ) :: Ξ := hsub (show φ ∈ [φ] by simp)
      rcases List.mem_cons.mp hhead with heq | hΞ
      · exact absurd heq (Literals.ne_all hAT)
      · refine .contraction (fun x hx => ?_) (.atom hAT)
        simp only [List.mem_singleton] at hx
        subst hx
        simp only [List.mem_cons]
        tauto
  | @identity α k rl v =>
      intro χ Ξ hsub n
      have hrel : Semiformula.rel rl v ∈ (∀¹ χ) :: Ξ :=
        hsub (show Semiformula.rel rl v ∈ [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
      have hnrel : Semiformula.nrel rl v ∈ (∀¹ χ) :: Ξ :=
        hsub (show Semiformula.nrel rl v ∈ [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
      rcases List.mem_cons.mp hrel with heq | hΞ1
      · exact absurd heq (ne_of_headTag (by simp only [headTag_rel, headTag_all]; decide))
      rcases List.mem_cons.mp hnrel with heq | hΞ2
      · exact absurd heq (ne_of_headTag (by simp only [headTag_nrel, headTag_all]; decide))
      refine .contraction (fun x hx => ?_) (.identity rl v)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [List.mem_cons]
      rcases hx with rfl | rfl
      · tauto
      · tauto
  | @verum α =>
      intro χ Ξ hsub n
      have hhead : (⊤ : Proposition LRA) ∈ (∀¹ χ) :: Ξ := hsub (show (⊤:Proposition LRA) ∈ [⊤] by simp)
      rcases List.mem_cons.mp hhead with heq | hΞ
      · exact absurd heq (ne_of_headTag (by simp only [headTag_verum, headTag_all]; decide))
      · refine .contraction (fun x hx => ?_) .verum
        simp only [List.mem_singleton] at hx
        subst hx
        simp only [List.mem_cons]
        tauto
  | @or α β φ ψ Γ hlt hprem ih =>
      intro χ Ξ hsub n
      have hX : (φ ⋎ ψ) ∈ Ξ := by
        have hhead : (φ ⋎ ψ) ∈ (∀¹ χ) :: Ξ := hsub (show (φ⋎ψ) ∈ (φ⋎ψ)::Γ by simp)
        rcases List.mem_cons.mp hhead with heq | hΞ
        · exact absurd heq (ne_of_headTag (by simp only [headTag_or, headTag_all]; decide))
        · exact hΞ
      have hΓ : Γ ⊆ (∀¹ χ) :: Ξ := fun x hx => hsub (List.mem_cons_of_mem _ hx)
      have hsub' : (φ :: ψ :: Γ) ⊆ (∀¹ χ) :: (φ :: ψ :: Ξ) := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · simp
        · simp
        · rcases List.mem_cons.mp (hΓ hx) with rfl | hx
          · simp
          · simp [hx]
      have hstep := ih hsub' n
      have hreorder : (I.inst χ n :: φ :: ψ :: Ξ) ⊆ (φ :: ψ :: I.inst χ n :: Ξ) := by
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      have hprem' : OmegaDerivableR A I ρ β (φ :: ψ :: I.inst χ n :: Ξ) :=
        .contraction hreorder hstep
      have hconcl : OmegaDerivableR A I ρ α ((φ ⋎ ψ) :: I.inst χ n :: Ξ) := .or hlt hprem'
      refine .contraction (fun x hx => ?_) hconcl
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | rfl | hx
      · tauto
      · tauto
      · tauto
  | @and α β γ φ ψ Γ h1 h2 d1 d2 ih1 ih2 =>
      intro χ Ξ hsub n
      have hX : (φ ⋏ ψ) ∈ Ξ := by
        have hhead : (φ ⋏ ψ) ∈ (∀¹ χ) :: Ξ := hsub (show (φ⋏ψ) ∈ (φ⋏ψ)::Γ by simp)
        rcases List.mem_cons.mp hhead with heq | hΞ
        · exact absurd heq (ne_of_headTag (by simp only [headTag_and, headTag_all]; decide))
        · exact hΞ
      have hΓ : Γ ⊆ (∀¹ χ) :: Ξ := fun x hx => hsub (List.mem_cons_of_mem _ hx)
      have hsub1 : (φ :: Γ) ⊆ (∀¹ χ) :: (φ :: Ξ) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases List.mem_cons.mp (hΓ hx) with rfl | hx
          · simp
          · simp [hx]
      have hsub2 : (ψ :: Γ) ⊆ (∀¹ χ) :: (ψ :: Ξ) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases List.mem_cons.mp (hΓ hx) with rfl | hx
          · simp
          · simp [hx]
      have hstep1 := ih1 hsub1 n
      have hstep2 := ih2 hsub2 n
      have hreorder1 : (I.inst χ n :: φ :: Ξ) ⊆ (φ :: I.inst χ n :: Ξ) := by
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      have hreorder2 : (I.inst χ n :: ψ :: Ξ) ⊆ (ψ :: I.inst χ n :: Ξ) := by
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      have hconcl : OmegaDerivableR A I ρ α ((φ ⋏ ψ) :: I.inst χ n :: Ξ) :=
        .and h1 h2 (.contraction hreorder1 hstep1) (.contraction hreorder2 hstep2)
      refine .contraction (fun x hx => ?_) hconcl
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | rfl | hx
      · tauto
      · tauto
      · tauto
  | @omegaRule α φ Γ β hf hprem ih =>
      intro χ Ξ hsub n
      by_cases heq : φ = χ
      · subst heq
        have hΓ : Γ ⊆ (∀¹ φ) :: Ξ := fun x hx => hsub (List.mem_cons_of_mem _ hx)
        have hsub' : (I.inst φ n :: Γ) ⊆ (∀¹ φ) :: (I.inst φ n :: Ξ) := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · simp
          · rcases List.mem_cons.mp (hΓ hx) with rfl | hx
            · simp
            · simp [hx]
        have hstep := ih n hsub' n
        have hdup : (I.inst φ n :: I.inst φ n :: Ξ) ⊆ (I.inst φ n :: Ξ) := by
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
        exact (.contraction hdup hstep : OmegaDerivableR A I ρ (β n) (I.inst φ n :: Ξ)).mono_ord
          (le_of_lt (hf n))
      · have hne : (∀¹ φ : Proposition LRA) ≠ ∀¹ χ := fun he => heq (by simpa using he)
        have hX : (∀¹ φ : Proposition LRA) ∈ Ξ := by
          have hhead : (∀¹ φ : Proposition LRA) ∈ (∀¹ χ) :: Ξ :=
            hsub (show (∀¹ φ : Proposition LRA) ∈ (∀¹ φ)::Γ by simp)
          rcases List.mem_cons.mp hhead with he | hΞ
          · exact absurd he hne
          · exact hΞ
        have hΓ : Γ ⊆ (∀¹ χ) :: Ξ := fun x hx => hsub (List.mem_cons_of_mem _ hx)
        have hfam : ∀ m : ℕ, OmegaDerivableR A I ρ (β m) (I.inst φ m :: I.inst χ n :: Ξ) := by
          intro m
          have hsubm : (I.inst φ m :: Γ) ⊆ (∀¹ χ) :: (I.inst φ m :: Ξ) := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · simp
            · rcases List.mem_cons.mp (hΓ hx) with rfl | hx
              · simp
              · simp [hx]
          have hstepm := ih m hsubm n
          have hreorder : (I.inst χ n :: I.inst φ m :: Ξ) ⊆ (I.inst φ m :: I.inst χ n :: Ξ) := by
            intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
          exact .contraction hreorder hstepm
        have hconcl : OmegaDerivableR A I ρ α ((∀¹ φ) :: I.inst χ n :: Ξ) :=
          .omegaRule β hf hfam
        refine .contraction (fun x hx => ?_) hconcl
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | rfl | hx
        · tauto
        · tauto
        · tauto
  | @exs α β φ Γ nc hlt hprem ih =>
      intro χ Ξ hsub n
      have hX : (∃¹ φ) ∈ Ξ := by
        have hhead : (∃¹ φ) ∈ (∀¹ χ) :: Ξ := hsub (show (∃¹ φ) ∈ (∃¹ φ)::Γ by simp)
        rcases List.mem_cons.mp hhead with heq | hΞ
        · exact absurd heq (ne_of_headTag (by simp only [headTag_exs, headTag_all]; decide))
        · exact hΞ
      have hΓ : Γ ⊆ (∀¹ χ) :: Ξ := fun x hx => hsub (List.mem_cons_of_mem _ hx)
      have hsub' : (I.inst φ nc :: Γ) ⊆ (∀¹ χ) :: (I.inst φ nc :: Ξ) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases List.mem_cons.mp (hΓ hx) with rfl | hx
          · simp
          · simp [hx]
      have hstep := ih hsub' n
      have hreorder : (I.inst χ n :: I.inst φ nc :: Ξ) ⊆ (I.inst φ nc :: I.inst χ n :: Ξ) := by
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      have hconcl : OmegaDerivableR A I ρ α ((∃¹ φ) :: I.inst χ n :: Ξ) :=
        .exs nc hlt (.contraction hreorder hstep)
      refine .contraction (fun x hx => ?_) hconcl
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | rfl | hx
      · tauto
      · tauto
      · tauto
  | @contraction α Δ Γc hsubc hd ih =>
      intro χ Ξ hsub n
      exact ih (fun x hx => hsub (hsubc hx)) n
  | @cut α β γ φ Γc Δc hrk h1 h2 d1 d2 ih1 ih2 =>
      intro χ Ξ hsub n
      have hΓc : Γc ⊆ (∀¹ χ) :: Ξ := fun x hx => hsub (List.mem_append.mpr (Or.inl hx))
      have hΔc : Δc ⊆ (∀¹ χ) :: Ξ := fun x hx => hsub (List.mem_append.mpr (Or.inr hx))
      have hsub1 : (φ :: Γc) ⊆ (∀¹ χ) :: (φ :: Ξ) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases List.mem_cons.mp (hΓc hx) with rfl | hx
          · simp
          · simp [hx]
      have hsub2 : (∼φ :: Δc) ⊆ (∀¹ χ) :: (∼φ :: Ξ) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases List.mem_cons.mp (hΔc hx) with rfl | hx
          · simp
          · simp [hx]
      have hstep1 := ih1 hsub1 n
      have hstep2 := ih2 hsub2 n
      have hreorder1 : (I.inst χ n :: φ :: Ξ) ⊆ (φ :: I.inst χ n :: Ξ) := by
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      have hreorder2 : (I.inst χ n :: ∼φ :: Ξ) ⊆ (∼φ :: I.inst χ n :: Ξ) := by
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      have hconcl : OmegaDerivableR A I ρ α ((I.inst χ n :: Ξ) ++ (I.inst χ n :: Ξ)) :=
        .cut hrk h1 h2 (.contraction hreorder1 hstep1) (.contraction hreorder2 hstep2)
      exact .contraction
        (by intro x hx; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto)
        hconcl
  | @pr α β a nc Γc ha hlt hprem ih =>
      intro χ Ξ hsub n
      have hX : memAt (lvl a) (I.num nc) (I.num a) ∈ Ξ := by
        have hhead : memAt (lvl a) (I.num nc) (I.num a) ∈ (∀¹ χ) :: Ξ :=
          hsub (show memAt (lvl a) (I.num nc) (I.num a) ∈
            memAt (lvl a) (I.num nc) (I.num a) :: Γc by simp)
        rcases List.mem_cons.mp hhead with heq | hΞ
        · exact absurd heq (ne_of_headTag (by simp only [headTag_memAt, headTag_all]; decide))
        · exact hΞ
      have hΓc : Γc ⊆ (∀¹ χ) :: Ξ := fun x hx => hsub (List.mem_cons_of_mem _ hx)
      have hsub' : (I.inst (body a) nc :: Γc) ⊆ (∀¹ χ) :: (I.inst (body a) nc :: Ξ) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases List.mem_cons.mp (hΓc hx) with rfl | hx
          · simp
          · simp [hx]
      have hstep := ih hsub' n
      have hreorder : (I.inst χ n :: I.inst (body a) nc :: Ξ) ⊆
          (I.inst (body a) nc :: I.inst χ n :: Ξ) := by
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      have hconcl : OmegaDerivableR A I ρ α
          (memAt (lvl a) (I.num nc) (I.num a) :: I.inst χ n :: Ξ) :=
        .pr ha hlt (.contraction hreorder hstep)
      refine .contraction (fun x hx => ?_) hconcl
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | rfl | hx
      · tauto
      · tauto
      · tauto
  | @npr α β a nc Γc ha hlt hprem ih =>
      intro χ Ξ hsub n
      have hX : nmemAt (lvl a) (I.num nc) (I.num a) ∈ Ξ := by
        have hhead : nmemAt (lvl a) (I.num nc) (I.num a) ∈ (∀¹ χ) :: Ξ :=
          hsub (show nmemAt (lvl a) (I.num nc) (I.num a) ∈
            nmemAt (lvl a) (I.num nc) (I.num a) :: Γc by simp)
        rcases List.mem_cons.mp hhead with heq | hΞ
        · exact absurd heq (ne_of_headTag (by simp only [headTag_nmemAt, headTag_all]; decide))
        · exact hΞ
      have hΓc : Γc ⊆ (∀¹ χ) :: Ξ := fun x hx => hsub (List.mem_cons_of_mem _ hx)
      have hsub' : (∼(I.inst (body a) nc) :: Γc) ⊆ (∀¹ χ) :: (∼(I.inst (body a) nc) :: Ξ) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases List.mem_cons.mp (hΓc hx) with rfl | hx
          · simp
          · simp [hx]
      have hstep := ih hsub' n
      have hreorder : (I.inst χ n :: ∼(I.inst (body a) nc) :: Ξ) ⊆
          (∼(I.inst (body a) nc) :: I.inst χ n :: Ξ) := by
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      have hconcl : OmegaDerivableR A I ρ α
          (nmemAt (lvl a) (I.num nc) (I.num a) :: I.inst χ n :: Ξ) :=
        .npr ha hlt (.contraction hreorder hstep)
      refine .contraction (fun x hx => ?_) hconcl
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | rfl | hx
      · tauto
      · tauto
      · tauto

/-- **∀-inversion.**  From `⊢^α_ρ (∀¹ φ) :: Γ`, derive `⊢^α_ρ I.inst φ n :: Γ`
for every `n`, at the same height and the same rank. -/
theorem invAll {α : O} {φ : Semiproposition LRA 1} {Γ : Sequent LRA}
    (h : OmegaDerivableR A I ρ α ((∀¹ φ) :: Γ)) (n : ℕ) :
    OmegaDerivableR A I ρ α (I.inst φ n :: Γ) :=
  invAllSub h (fun _ hx => hx) n

end OmegaDerivableR

/-! ### Finitary theorem to uniform-height numeral instances -/

/-- **The sentence embedding commutes with `∀¹`.**  `Rewriting.emb` is not
*definitionally* natural in the quantifier (`Rew.q_emb` is a lemma, not `rfl`,
exactly as `Gentzen/AxiomsLogic.lean`'s `emb_relExtX` records for a doubly
quantified sentence); this is the single instance the replay chain below
needs. -/
theorem embAll (χ : Semiformula LRA Empty 1) :
    (Rewriting.emb (∀¹ χ) : Proposition LRA) = ∀¹ (Rewriting.emb χ : Semiformula LRA ℕ 1) := by
  show (Rew.emb ▹ (∀¹ χ) : Semiformula LRA ℕ 0) = ∀¹ (Rew.emb ▹ χ)
  rw [Rewriting.app_all, Rew.q_emb]

/-- **Step 1 of `(D^β)`, generic in the theory.**  If `T` proves the sentence
`∀¹ φ`, and every axiom of `T` is derivable in `RA_∞` below the rank `ρ`, there
is a single height `α` deriving `evR ((emb φ)/[num n])` for *every* numeral `n`
— the replay-and-cut chain (`OmegaDerivableR.provable_omegaDerivable_of`)
composed with ∀-inversion (`OmegaDerivableR.invAll`). -/
theorem uniformHeight_of_provable_all_of (T : Theory LRA) {ρ : Gamma0Note}
    (hax : ∀ σ ∈ T, ∃ β : Gamma0Note, OmegaDerivableR trueArithLitsR evInstR 0 β
        [evR (Rewriting.emb σ : Proposition LRA)])
    (hrk : ∀ σ ∈ T, rank (evR (Rewriting.emb σ : Proposition LRA)) < ρ)
    {φ : Semiformula LRA Empty 1} (h : T ⊢! (∀¹ φ : Sentence LRA)) :
    ∃ α : Gamma0Note, ∀ n : ℕ,
      OmegaDerivableR trueArithLitsR evInstR ρ α
        [evR ((Rewriting.emb φ : Semiformula LRA ℕ 1)/[num n])] := by
  obtain ⟨α, hα⟩ := provable_omegaDerivable_of T hax hrk h
  rw [embAll, evR_all] at hα
  refine ⟨α, fun n => ?_⟩
  have hstep := OmegaDerivableR.invAll (Γ := []) hα n
  simpa [evInstR_inst_ev] using hstep

/-- **The `RAlt ν` instance of step 1.** -/
theorem uniformHeight_of_provable_all {ν : Lv} (hν : 1 ≤ ν) {φ : Semiformula LRA Empty 1}
    (h : RAlt ν ⊢! (∀¹ φ : Sentence LRA)) :
    ∃ α : Gamma0Note, ∀ n : ℕ,
      OmegaDerivableR trueArithLitsR evInstR (Gamma0Note.blkTop ν) α
        [evR ((Rewriting.emb φ : Semiformula LRA ℕ 1)/[num n])] := by
  obtain ⟨α, hα⟩ := provable_omegaDerivable hν h
  rw [embAll, evR_all] at hα
  refine ⟨α, fun n => ?_⟩
  have hstep := OmegaDerivableR.invAll (Γ := []) hα n
  simpa [evInstR_inst_ev] using hstep

/-! ### Axiom audit -/

#print axioms OmegaDerivableR.weakening
#print axioms OmegaDerivableR.exchange
#print axioms OmegaDerivableR.cutR
#print axioms OmegaDerivableR.omegaRuleUniform
#print axioms OmegaDerivableR.existsInstR
#print axioms OmegaDerivableR.invAllSub
#print axioms OmegaDerivableR.invAll
#print axioms embAll
#print axioms uniformHeight_of_provable_all_of
#print axioms uniformHeight_of_provable_all

end Ramified

end OrdinalAnalysis
