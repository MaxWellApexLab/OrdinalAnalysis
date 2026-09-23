/-
  The one case of the reduction lemma that decides D1 against D2.

  `gamma0_design.md` §4 G2 asks the prototype for "one (Pr)/(Pr) reduction case"
  and a rank inequality for the unfolding of a code.  The second is
  `Ramified/Rank.lean`'s `rank_body_lt_memRank`; this file is the first.

  `ReductionStatement` records the shape of the full lemma — the same shape as
  `Omega/Reduction.lean`'s `reduction` and `ACAOmega/Reduction.lean`'s, with the
  natural-number cut rank replaced by the ordinal one:

      rank φ ≤ ρ → ⊢^β Γ₀ → Γ₀ ⊆ φ :: Θ → ⊢^γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ → ⊢^{redOrd β γ} Θ

  and `RedIHR` packages it below a bound on the symmetric measure `β ⊕ γ`,
  exactly as `RedIHΩ`/`RedIH₂` do, because the principal cases consume it with
  the two sides swapped.

  `reduction_pr_principal` is the new principal case.  Its content:

  * the cut formula is a set atom `n̄ ∈̇_ν ā` with `ν = lvl a` and `Good a`;
  * both sides are (Pr) inferences on it, so the sub-derivations give the
    unfolding `A_a(n̄)` and its negation at strictly smaller heights;
  * `rank (A_a(n̄)) ≤ rank (body a) < ω·(ν − 1) ⊕ stage a = rank (n̄ ∈̇_ν ā) ≤ ρ`
    (`rank_inst_body_lt_rank_prAtom`), so a cut on the unfolding is legal at the
    very rank the atom itself is being cut at — *this is the whole design*;
  * the height bookkeeping closes with `redOrd`, with room to spare.

  The last point is worth spelling out, because it is the cheapest of the five
  principal cases rather than the most expensive.  The propositional cases of
  `Omega/Reduction.lean` perform two *nested* cuts and are the sole reason the
  delivered ordinal is the doubled sum `redOrd β γ = (β ⊕ γ) ⊕ (β ⊕ γ)` rather
  than `β ⊕ γ`.  (Pr)/(Pr) performs **one** cut, like the ω-rule/`exs` pair:
  two appeals to the induction hypothesis (once per side, with the whole
  derivation on one side and a premise on the other) followed by a single cut on
  the unfolding.  So (Pr) adds no new demand on the ordinal arithmetic at all —
  `redOrd_lt_left` and `redOrd_lt_right`, both already in
  `Ordinal/Notation.lean`, are the only facts used.

  `reduction_pr_atom_absurd` records the one genuinely new side condition the
  prototype turned up: an axiom must not be a set atom (`MemFree`), or the
  (Pr)/axiom pair would be an irreducible principal case.  `Literals` does not
  give this for free — a set atom *is* a literal — and it is the exact analogue
  of `StandardLX.lean`'s `trueArithLits_xfree`.
-/
import OrdinalAnalysis.Ramified.Calculus

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Derivation

namespace OmegaDerivableR

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals LRA} {I : InstantiationR}

/-! ### The shape of the reduction lemma -/

/-- **The full reduction lemma, as a statement.**  Not proved here: the
prototype proves only the principal case that decides the design. -/
def ReductionStatement (A : Literals LRA) (I : InstantiationR) (ρ : Gamma0Note) : Prop :=
  ∀ (β γ : O) {Γ₀ Δ₀ Θ : Sequent LRA} {φ : Proposition LRA},
    rank φ ≤ ρ →
    OmegaDerivableR A I ρ β Γ₀ → Γ₀ ⊆ φ :: Θ →
    OmegaDerivableR A I ρ γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ →
      OmegaDerivableR A I ρ (OrdinalNotation.redOrd β γ) Θ

/-- The reduction lemma below a bound on the symmetric measure `β ⊕ γ`, the form
the principal cases take as an argument.  `Omega/Reduction.lean`'s `RedIHΩ` and
`ACAOmega/Reduction.lean`'s `RedIH₂`, verbatim. -/
def RedIHR (A : Literals LRA) (I : InstantiationR) (ρ : Gamma0Note) (s : O) : Prop :=
  ∀ (β γ : O), OrdinalNotation.nadd β γ < s →
    ∀ {Γ₀ : Sequent LRA}, OmegaDerivableR A I ρ β Γ₀ →
      ∀ {φ : Proposition LRA}, rank φ ≤ ρ →
      ∀ {Θ Δ₀ : Sequent LRA}, Γ₀ ⊆ φ :: Θ →
        OmegaDerivableR A I ρ γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ →
          OmegaDerivableR A I ρ (OrdinalNotation.redOrd β γ) Θ

/-! ### The principal (Pr)/(Pr) case -/

set_option maxHeartbeats 1000000 in
/-- **The principal (Pr)/(Pr) case of the reduction lemma.**

Both derivations end in a predicator rule on the same atom `n̄ ∈̇_{lvl a} ā`:
the left concludes it by (Pr) from the unfolding `A_a(n̄)` at height `β₀ < β`,
the right concludes its negation by (Pr⁻) from `∼A_a(n̄)` at height `γ₀ < γ`.

The proof is two appeals to the induction hypothesis and one cut:

1. the whole left derivation against the right *premise*, at measure `β ⊕ γ₀`,
   with the target extended by `∼A_a(n̄)` — giving `⊢^{redOrd β γ₀} ∼A_a(n̄), Θ`;
2. symmetrically, the whole right derivation against the left *premise*, at
   measure `β₀ ⊕ γ` — giving `⊢^{redOrd β₀ γ} A_a(n̄), Θ`;
3. cut on `A_a(n̄)`, legal because `rank (A_a(n̄)) < rank (n̄ ∈̇ ā) ≤ ρ`,
   and both heights are below `redOrd β γ`.

Step 3 is where the whole of D2 is decided, and it is `rank_body_lt_memRank`. -/
theorem reduction_pr_principal {ρ : Gamma0Note} {s β γ β₀ γ₀ : O}
    (ih2 : RedIHR A I ρ s) (hs : OrdinalNotation.nadd β γ ≤ s)
    {a n : ℕ} (ha : Good a) (hr : rank (prAtom I a n) ≤ ρ)
    {Γ₁ Δ₁ Θ : Sequent LRA}
    (hβ₀ : β₀ < β) (hγ₀ : γ₀ < γ)
    (hL : OmegaDerivableR A I ρ β₀ (I.inst (body a) n :: Γ₁))
    (hΓ : Γ₁ ⊆ prAtom I a n :: Θ)
    (hR : OmegaDerivableR A I ρ γ₀ (∼(I.inst (body a) n) :: Δ₁))
    (hΔ : Δ₁ ⊆ ∼(prAtom I a n) :: Θ) :
    OmegaDerivableR A I ρ (OrdinalNotation.redOrd β γ) Θ := by
  -- The two conclusions, rebuilt from their premises.
  have hLfull : OmegaDerivableR A I ρ β (prAtom I a n :: Γ₁) :=
    OmegaDerivableR.pr ha hβ₀ hL
  have hRfull : OmegaDerivableR A I ρ γ (∼(prAtom I a n) :: Δ₁) :=
    OmegaDerivableR.npr ha hγ₀ hR
  -- Step 1: whole left against the right premise, target `∼A_a(n̄) :: Θ`.
  have k₁ : OmegaDerivableR A I ρ (OrdinalNotation.redOrd β γ₀)
      (∼(I.inst (body a) n) :: Θ) := by
    refine ih2 β γ₀
      (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right β hγ₀) hs)
      hLfull hr (Θ := ∼(I.inst (body a) n) :: Θ) ?_ hR ?_
    · intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · tauto
      · have := hΓ hx
        simp only [List.mem_cons] at this
        tauto
    · intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · tauto
      · have := hΔ hx
        simp only [List.mem_cons] at this
        tauto
  -- Step 2: whole right against the left premise, target `A_a(n̄) :: Θ`.
  have k₂ : OmegaDerivableR A I ρ (OrdinalNotation.redOrd β₀ γ)
      (I.inst (body a) n :: Θ) := by
    refine ih2 β₀ γ
      (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hβ₀) hs)
      hL hr (Θ := I.inst (body a) n :: Θ) ?_ hRfull ?_
    · intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · tauto
      · have := hΓ hx
        simp only [List.mem_cons] at this
        tauto
    · intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · tauto
      · have := hΔ hx
        simp only [List.mem_cons] at this
        tauto
  -- Step 3: cut on the unfolding.  This is the step `rank_body_lt_memRank` buys.
  have hrank : rank (I.inst (body a) n) < ρ :=
    lt_of_lt_of_le (rank_inst_body_lt_rank_prAtom ha n) hr
  exact of_append_self
    (OmegaDerivableR.cut hrank
      (OrdinalNotation.redOrd_lt_left γ hβ₀)
      (OrdinalNotation.redOrd_lt_right β hγ₀) k₂ k₁)

/-- **The principal case as the dispatcher will meet it.**

The reduction lemma does not get the two sides handed to it with matching codes;
it gets a left (Pr) on `a, n` and a right (Pr⁻) on some `a', n'` together with
the equation saying their conclusions match.  `prAtom_inj` turns that equation
into `a' = a`, `n' = n` — using only `InstantiationR.num_inj`, since the level is
read off the relation symbol — and the previous lemma finishes.

So the (Pr)/(Pr) case closes end to end, not just modulo matching. -/
theorem reduction_pr_principal_dispatch {ρ : Gamma0Note} {s β γ β₀ γ₀ : O}
    (ih2 : RedIHR A I ρ s) (hs : OrdinalNotation.nadd β γ ≤ s)
    {a n a' n' : ℕ} (ha : Good a) (hr : rank (prAtom I a n) ≤ ρ)
    (hmatch : nmemAt (lvl a') (I.num n') (I.num a') = ∼(prAtom I a n))
    {Γ₁ Δ₁ Θ : Sequent LRA}
    (hβ₀ : β₀ < β) (hγ₀ : γ₀ < γ)
    (hL : OmegaDerivableR A I ρ β₀ (I.inst (body a) n :: Γ₁))
    (hΓ : Γ₁ ⊆ prAtom I a n :: Θ)
    (hR : OmegaDerivableR A I ρ γ₀ (∼(I.inst (body a') n') :: Δ₁))
    (hΔ : Δ₁ ⊆ ∼(prAtom I a n) :: Θ) :
    OmegaDerivableR A I ρ (OrdinalNotation.redOrd β γ) Θ := by
  obtain ⟨rfl, rfl⟩ := nprAtom_inj hmatch
  exact reduction_pr_principal ih2 hs ha hr hβ₀ hγ₀ hL hΓ hR hΔ

/-! ### The side condition the prototype turned up -/

/-- **A (Pr) atom is never an axiom**, given `MemFree`.

The reduction lemma's `atom` case asks: what if the right derivation *is* an
axiom, and that axiom is the negation of the cut formula?  When the cut formula
is a (Pr) atom, the negation is `n̄ ∉̇_ν ā` — a literal, hence not excluded by
`Literals` alone.  `MemFree` excludes it, and this lemma is the form the `atom`
case of the (Pr) reduction will consume. -/
theorem reduction_pr_atom_absurd (hA : MemFree A) {a n : ℕ}
    {χ : Proposition LRA} (hχ : A.T χ) (he : χ = ∼(prAtom I a n)) : False :=
  MemFree.ne_nmemAt hA hχ (lvl a) (I.num n) (I.num a) he

/-- The positive twin. -/
theorem reduction_pr_atom_absurd' (hA : MemFree A) {a n : ℕ}
    {χ : Proposition LRA} (hχ : A.T χ) (he : χ = prAtom I a n) : False :=
  MemFree.ne_memAt hA hχ (lvl a) (I.num n) (I.num a) he

end OmegaDerivableR

end Ramified

end OrdinalAnalysis
