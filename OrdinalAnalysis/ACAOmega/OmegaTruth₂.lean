/-
  ω-completeness for the **set-free fragment** of `ACA_∞`.

  This is `Gentzen/OmegaTruth.lean` transported to the second-order syntax.  The
  first-order file proves "every closed `X`-free sentence true in `ℕ` has a
  cut-free ω-derivation of height its own complexity"; here the same statement is
  proved for `Proposition ℒₒᵣ` with `XFree` replaced by `CodedOrder₂.SetFree` —
  no set atom *and* no set quantifier — and with the conclusion already in the
  evaluating calculus.

  Four things about the shape.

  * **No transport step.**  The first-order development proves ω-completeness for
    `Instantiation.raw` and then moves it along `ev` with the machinery of
    `Omega/Transfer.lean`.  There is no second-order `Transfer`, and none is
    needed: the induction is run directly against `evInst₂`, with the conclusion
    `[ev₂ φ]` rather than `[φ]`.  Every clause matches — `ev₂` commutes with all
    twelve connectives (`ev₂_and`, `ev₂_all₁`, …), and `evInst₂_inst_ev` says the
    `n`-th instance of the *evaluated* body is the evaluated `n`-th instance,
    which is exactly the induction hypothesis.  The atomic case is
    `trueArithLits₂_ev₂`, which is where the normal-form side condition
    `ev₂ φ = φ` of the axiom set is discharged: `ev₂ φ` is `ev₂`-fixed by
    `ev₂_idem` whatever `φ` was.

  * **The height is finite.**  `complexity` drops strictly at every rule, and
    `complexity_rew₂` (proved here — Foundation has the first-order lemma only)
    says a rewriting does not change it, so the ω-rule's premises
    `ev₂ (φ/[n̄])` all have complexity `φ.complexity`, uniformly in `n`.  A single
    `OrdinalNotation.ofNat` therefore bounds them all, and the whole file runs at
    heights in an arbitrary `[OrdinalNotation O]`: nothing above `ω` is used.

  * **Closedness has to be syntactic, and set-freeness does not cover it.**
    `SetFree` forbids set variables; it says nothing about free *number*
    variables, and the atomic axioms of `trueArithLits₂` are literals with closed
    arguments.  `NumClosed` is that missing half — "every term occurring in `φ`
    has no `&x`" — defined by recursion so that it survives the numeral
    substitution of the ω-rule.

  * **Every sequent is a singleton.**  The induction derives `[ev₂ φ]` and
    nothing else; the only structural step is the weakening `[φ] ⊆ [φ, ψ]` that
    the `or` rule needs, supplied by `OmegaDerivable₂.contraction`.

  Contents.

    `complexity_rew₂`, `complexity_neg₂`   complexity under rewriting and negation
    `NumClosed`                            no free number variable
    `numClosed_rew`, `numClosed_subst_numAt`  …and its closure properties
    `numClosed_lift`                       everything lifted from a closed
                                           first-order formula is `NumClosed`
    `isArithLit₂_of_numClosed_rel`         the bridge to the atomic axioms
    `cases₀`                               case analysis on a `Proposition`
    `hgt₂`                                 the height
    `omega_complete₂_ev`                   **the master lemma**
    `omega_complete₂`                      its form at an `ev₂`-fixed formula
    `omega_complete₂_ev_neg`               the negative form
    `omega_complete₂_liftEmb`              the form the `𝗘𝗤`/`𝗣𝗔⁻` rows consume
-/
import OrdinalAnalysis.ACAOmega.CodedOrder₂
import OrdinalAnalysis.Gentzen.LowerSyntax

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA

namespace OmegaTruth₂

/-! ### Complexity under rewriting and negation

Foundation proves `Semiformula.complexity_rew` for the first-order syntax only;
the two lemmas below are the second-order copies, and they are what makes the
ω-rule's premises uniformly bounded. -/

/-- **A first-order rewriting does not change the complexity.** -/
@[simp] theorem complexity_rew₂ {L : FirstOrder.Language} {Ξ ξ₁ ξ₂ : Type*}
    {N n₁ n₂ : ℕ} (ω : FirstOrder.Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N n₁) :
    (ω ▹ φ).complexity = φ.complexity := by
  induction φ using Semiformula.rec' generalizing n₂ <;>
    simp [Semiformula.rew_rel, Semiformula.rew_nrel, *]

/-- **Negation does not change the complexity.** -/
@[simp] theorem complexity_neg₂ {L : FirstOrder.Language} {Ξ ξ : Type*} {N n : ℕ}
    (φ : Semiformula L Ξ ξ N n) : (∼φ).complexity = φ.complexity := by
  induction φ using Semiformula.rec' <;> simp [*]

/-! ### No free number variable

`SetFree` (`CodedOrder₂.lean`) forbids set variables; this predicate forbids free
*number* variables.  Bound number variables are permitted — the recursion has to
pass under `∀¹`/`∃¹` — so the condition is stated on each term as
`freeVariables = ∅` rather than as `Ground`. -/

/-- **`φ` has no free number variable**: every term occurring in it is closed. -/
def NumClosed {N n : ℕ} : Semiformula ℒₒᵣ ℕ ℕ N n → Prop
  |  .rel _ v => ∀ i, (v i).freeVariables = ∅
  | .nrel _ v => ∀ i, (v i).freeVariables = ∅
  |    t ∈# _ => t.freeVariables = ∅
  |    t ∉# _ => t.freeVariables = ∅
  |    t ∈& _ => t.freeVariables = ∅
  |    t ∉& _ => t.freeVariables = ∅
  |         ⊤ => True
  |         ⊥ => True
  |     φ ⋏ ψ => NumClosed φ ∧ NumClosed ψ
  |     φ ⋎ ψ => NumClosed φ ∧ NumClosed ψ
  |      ∀¹ φ => NumClosed φ
  |      ∃¹ φ => NumClosed φ
  |      ∀² φ => NumClosed φ
  |      ∃² φ => NumClosed φ

section NumClosedSimp

variable {N n : ℕ}

@[simp] theorem numClosed_rel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    NumClosed (.rel r v : Semiformula ℒₒᵣ ℕ ℕ N n) ↔ ∀ i, (v i).freeVariables = ∅ := Iff.rfl

@[simp] theorem numClosed_nrel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    NumClosed (.nrel r v : Semiformula ℒₒᵣ ℕ ℕ N n) ↔ ∀ i, (v i).freeVariables = ∅ := Iff.rfl

@[simp] theorem numClosed_bvar (X : Fin N) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    NumClosed (t ∈# X : Semiformula ℒₒᵣ ℕ ℕ N n) ↔ t.freeVariables = ∅ := Iff.rfl

@[simp] theorem numClosed_nbvar (X : Fin N) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    NumClosed (t ∉# X : Semiformula ℒₒᵣ ℕ ℕ N n) ↔ t.freeVariables = ∅ := Iff.rfl

@[simp] theorem numClosed_fvar (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    NumClosed (t ∈& X : Semiformula ℒₒᵣ ℕ ℕ N n) ↔ t.freeVariables = ∅ := Iff.rfl

@[simp] theorem numClosed_nfvar (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    NumClosed (t ∉& X : Semiformula ℒₒᵣ ℕ ℕ N n) ↔ t.freeVariables = ∅ := Iff.rfl

@[simp] theorem numClosed_verum : NumClosed (⊤ : Semiformula ℒₒᵣ ℕ ℕ N n) := trivial

@[simp] theorem numClosed_falsum : NumClosed (⊥ : Semiformula ℒₒᵣ ℕ ℕ N n) := trivial

@[simp] theorem numClosed_and (φ ψ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    NumClosed (φ ⋏ ψ) ↔ NumClosed φ ∧ NumClosed ψ := Iff.rfl

@[simp] theorem numClosed_or (φ ψ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    NumClosed (φ ⋎ ψ) ↔ NumClosed φ ∧ NumClosed ψ := Iff.rfl

@[simp] theorem numClosed_all₁ (φ : Semiformula ℒₒᵣ ℕ ℕ N (n + 1)) :
    NumClosed (∀¹ φ) ↔ NumClosed φ := Iff.rfl

@[simp] theorem numClosed_exs₁ (φ : Semiformula ℒₒᵣ ℕ ℕ N (n + 1)) :
    NumClosed (∃¹ φ) ↔ NumClosed φ := Iff.rfl

@[simp] theorem numClosed_all₂ (φ : Semiformula ℒₒᵣ ℕ ℕ (N + 1) n) :
    NumClosed (∀² φ) ↔ NumClosed φ := Iff.rfl

@[simp] theorem numClosed_exs₂ (φ : Semiformula ℒₒᵣ ℕ ℕ (N + 1) n) :
    NumClosed (∃² φ) ↔ NumClosed φ := Iff.rfl

end NumClosedSimp

/-- Closedness is invariant under negation: de Morgan swaps constructors but
never touches a term. -/
@[simp] theorem numClosed_neg {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    NumClosed (∼φ) ↔ NumClosed φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- The side condition of `numClosed_rew` passes under a binder. -/
theorem freeVariables_q_eq_empty {m₁ m₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ m₁ ℕ m₂)
    (hb : ∀ i : Fin m₁, (ω #i).freeVariables = ∅) :
    ∀ i : Fin (m₁ + 1), (ω.q #i).freeVariables = ∅ := by
  intro i
  induction i using Fin.cases with
  | zero => simp
  | succ j => simpa using hb j

/-- **Closedness survives a rewriting whose bound-variable images are closed**,
with the rewriting quantified inside so that the induction may change it. -/
theorem numClosed_rew_all {N n₁ : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n₁) :
    ∀ (n₂ : ℕ) (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂), NumClosed φ →
      (∀ i : Fin n₁, (ω #i).freeVariables = ∅) → NumClosed (ω ▹ φ) := by
  induction φ using Semiformula.rec' with
  | hRel r v =>
      intro n₂ ω h hb
      simp only [Semiformula.rew_rel, numClosed_rel]
      intro i
      exact Gentzen.LowerSyntax.freeVariables_rew_term_eq_empty ω (h i) hb
  | hNrel r v =>
      intro n₂ ω h hb
      simp only [Semiformula.rew_nrel, numClosed_nrel]
      intro i
      exact Gentzen.LowerSyntax.freeVariables_rew_term_eq_empty ω (h i) hb
  | hBvar X t =>
      intro n₂ ω h hb
      simp only [Semiformula.rew_bvar, numClosed_bvar]
      exact Gentzen.LowerSyntax.freeVariables_rew_term_eq_empty ω h hb
  | hNbvar X t =>
      intro n₂ ω h hb
      simp only [Semiformula.rew_nbvar, numClosed_nbvar]
      exact Gentzen.LowerSyntax.freeVariables_rew_term_eq_empty ω h hb
  | hFvar X t =>
      intro n₂ ω h hb
      simp only [Semiformula.rew_fvar, numClosed_fvar]
      exact Gentzen.LowerSyntax.freeVariables_rew_term_eq_empty ω h hb
  | hNfvar X t =>
      intro n₂ ω h hb
      simp only [Semiformula.rew_nfvar, numClosed_nfvar]
      exact Gentzen.LowerSyntax.freeVariables_rew_term_eq_empty ω h hb
  | hVerum => intro n₂ ω _ _; simp
  | hFalsum => intro n₂ ω _ _; simp
  | hAnd φ ψ ihφ ihψ =>
      intro n₂ ω h hb
      simp only [LogicalConnective.HomClass.map_and, numClosed_and]
      exact ⟨ihφ n₂ ω h.1 hb, ihψ n₂ ω h.2 hb⟩
  | hOr φ ψ ihφ ihψ =>
      intro n₂ ω h hb
      simp only [LogicalConnective.HomClass.map_or, numClosed_or]
      exact ⟨ihφ n₂ ω h.1 hb, ihψ n₂ ω h.2 hb⟩
  | hAll₁ φ ih =>
      intro n₂ ω h hb
      simp only [Semiformula.rew_all₀, numClosed_all₁]
      exact ih (n₂ + 1) ω.q h (freeVariables_q_eq_empty ω hb)
  | hExs₁ φ ih =>
      intro n₂ ω h hb
      simp only [Semiformula.rew_exs₀, numClosed_exs₁]
      exact ih (n₂ + 1) ω.q h (freeVariables_q_eq_empty ω hb)
  | hAll₂ φ ih =>
      intro n₂ ω h hb
      simp only [Semiformula.rew_all₁, numClosed_all₂]
      exact ih n₂ ω h hb
  | hExs₂ φ ih =>
      intro n₂ ω h hb
      simp only [Semiformula.rew_exs₁, numClosed_exs₂]
      exact ih n₂ ω h hb

/-- **Closedness survives a rewriting whose bound-variable images are closed.**
This is what the ω-rule needs: the premises `φ/[n̄]` are closed whenever `∀¹ φ`
is. -/
theorem numClosed_rew {N n₁ n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    {φ : Semiformula ℒₒᵣ ℕ ℕ N n₁} (h : NumClosed φ)
    (hb : ∀ i : Fin n₁, (ω #i).freeVariables = ∅) : NumClosed (ω ▹ φ) :=
  numClosed_rew_all φ n₂ ω h hb

/-- Numerals are closed terms. -/
@[simp] theorem freeVariables_numAt {n : ℕ} (m : ℕ) :
    (numAt m : FirstOrder.Semiterm ℒₒᵣ ℕ n).freeVariables = ∅ :=
  freeVariables_of_ground (ground_numAt m)

/-- The instance of a closed body by a numeral is closed. -/
theorem numClosed_subst_numAt {N n : ℕ} {φ : Semiformula ℒₒᵣ ℕ ℕ N 1} (h : NumClosed φ)
    (m : ℕ) : NumClosed (φ/[(numAt m : FirstOrder.Semiterm ℒₒᵣ ℕ n)]) := by
  refine numClosed_rew (FirstOrder.Rew.subst ![numAt m]) h (fun i => ?_)
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp

/-! ### Lifted first-order formulas -/

private theorem closed_args {k n : ℕ} {v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n}
    (hc : (Finset.biUnion Finset.univ fun i => (v i).freeVariables) = (∅ : Finset ℕ))
    (i : Fin k) : (v i).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hmem : x ∈ (Finset.biUnion Finset.univ fun i => (v i).freeVariables) :=
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  rw [hc] at hmem
  exact Finset.notMem_empty x hmem

/-- **A lift of a closed first-order formula is closed.** -/
theorem numClosed_lift {N n : ℕ} :
    ∀ {φ : FirstOrder.Semiformula ℒₒᵣ ℕ n}, φ.freeVariables = ∅ →
      NumClosed (lift φ : Semiformula ℒₒᵣ ℕ ℕ N n) := by
  intro φ
  induction φ using FirstOrder.Semiformula.rec' with
  | hverum => intro _; simp
  | hfalsum => intro _; simp
  | hrel r v =>
      intro h
      rw [FirstOrder.Semiformula.freeVariables_rel] at h
      simpa using closed_args h
  | hnrel r v =>
      intro h
      rw [FirstOrder.Semiformula.freeVariables_nrel] at h
      simpa using closed_args h
  | hand φ ψ ihφ ihψ =>
      intro h
      rw [FirstOrder.Semiformula.freeVariables_and, Finset.union_eq_empty] at h
      simpa using ⟨ihφ h.1, ihψ h.2⟩
  | hor φ ψ ihφ ihψ =>
      intro h
      rw [FirstOrder.Semiformula.freeVariables_or, Finset.union_eq_empty] at h
      simpa using ⟨ihφ h.1, ihψ h.2⟩
  | hall φ ih =>
      intro h
      rw [FirstOrder.Semiformula.freeVariables_all] at h
      simpa using ih h
  | hexs φ ih =>
      intro h
      rw [FirstOrder.Semiformula.freeVariables_exs] at h
      simpa using ih h

/-! ### From a closed set-free atom to an axiom -/

theorem isArithLit₂_of_numClosed_rel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.SyntacticTerm ℒₒᵣ)
    (hc : NumClosed (Semiformula.rel r v : Proposition ℒₒᵣ)) :
    IsArithLit₂ (Semiformula.rel r v) :=
  isArithLit₂_rel r v hc

theorem isArithLit₂_of_numClosed_nrel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.SyntacticTerm ℒₒᵣ)
    (hc : NumClosed (Semiformula.nrel r v : Proposition ℒₒᵣ)) :
    IsArithLit₂ (Semiformula.nrel r v) :=
  isArithLit₂_nrel r v hc

/-! ### Case analysis on a proposition

`Semiformula.cases'` is stated for the whole family `∀ N n, Semiformula L Ξ ξ N n`,
which does not fit a goal whose indices are the literals `0, 0`.  The
specialisation below is stated in *connective* form, so that the `simp` lemmas of
`SetFree`, `NumClosed`, `TrueN₂`, `complexity` and `ev₂` — all of which are
indexed by the connective — fire on the resulting goals. -/

theorem cases₀ {C : Proposition ℒₒᵣ → Prop}
    (hrel : ∀ (k : ℕ) (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
      (v : Fin k → FirstOrder.SyntacticTerm ℒₒᵣ), C (Semiformula.rel r v))
    (hnrel : ∀ (k : ℕ) (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
      (v : Fin k → FirstOrder.SyntacticTerm ℒₒᵣ), C (Semiformula.nrel r v))
    (hbvar : ∀ (X : Fin 0) (t : FirstOrder.SyntacticTerm ℒₒᵣ), C (t ∈# X))
    (hnbvar : ∀ (X : Fin 0) (t : FirstOrder.SyntacticTerm ℒₒᵣ), C (t ∉# X))
    (hfvar : ∀ (X : ℕ) (t : FirstOrder.SyntacticTerm ℒₒᵣ), C (t ∈& X))
    (hnfvar : ∀ (X : ℕ) (t : FirstOrder.SyntacticTerm ℒₒᵣ), C (t ∉& X))
    (hverum : C ⊤) (hfalsum : C ⊥)
    (hand : ∀ φ ψ : Proposition ℒₒᵣ, C (φ ⋏ ψ))
    (hor : ∀ φ ψ : Proposition ℒₒᵣ, C (φ ⋎ ψ))
    (hall₁ : ∀ φ : Semiproposition ℒₒᵣ 0 1, C (∀¹ φ))
    (hexs₁ : ∀ φ : Semiproposition ℒₒᵣ 0 1, C (∃¹ φ))
    (hall₂ : ∀ φ : Semiproposition ℒₒᵣ 1 0, C (∀² φ))
    (hexs₂ : ∀ φ : Semiproposition ℒₒᵣ 1 0, C (∃² φ)) :
    ∀ φ : Proposition ℒₒᵣ, C φ
  | Semiformula.rel r v => hrel _ r v
  | Semiformula.nrel r v => hnrel _ r v
  | Semiformula.bvar X t => hbvar X t
  | Semiformula.nbvar X t => hnbvar X t
  | Semiformula.fvar X t => hfvar X t
  | Semiformula.nfvar X t => hnfvar X t
  | Semiformula.verum => hverum
  | Semiformula.falsum => hfalsum
  | Semiformula.and φ ψ => hand φ ψ
  | Semiformula.or φ ψ => hor φ ψ
  | Semiformula.all₁ φ => hall₁ φ
  | Semiformula.exs₁ φ => hexs₁ φ
  | Semiformula.all₂ φ => hall₂ φ
  | Semiformula.exs₂ φ => hexs₂ φ

/-! ### The master lemma -/

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- The ω-height assigned to a formula: its complexity, as a notation.

Strictly decreasing at every rule of the proof below, and — by
`complexity_rew₂` and `complexity_ev₂` — *constant* across the premises of the
ω-rule, which is what lets a single finite ordinal bound all of them. -/
def hgt₂ (φ : Proposition ℒₒᵣ) : O := OrdinalNotation.ofNat φ.complexity

@[simp] theorem hgt₂_neg (φ : Proposition ℒₒᵣ) : (hgt₂ (∼φ) : O) = hgt₂ φ := by
  simp [hgt₂]

@[simp] theorem hgt₂_ev₂ (φ : Proposition ℒₒᵣ) : (hgt₂ (ev₂ φ) : O) = hgt₂ φ := by
  simp [hgt₂]

/-- The induction, with the height fixed by an external bound on the complexity
so that the recursion is on `ℕ` rather than on the formula. -/
private theorem omega_complete₂_aux :
    ∀ (c : ℕ) (φ : Proposition ℒₒᵣ), φ.complexity ≤ c → SetFree φ → NumClosed φ →
      TrueN₂ φ →
      OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (OrdinalNotation.ofNat c) [ev₂ φ] := by
  intro c
  induction c with
  | zero =>
      intro φ
      refine cases₀ (C := fun φ => φ.complexity ≤ 0 → SetFree φ → NumClosed φ → TrueN₂ φ →
        OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (OrdinalNotation.ofNat 0) [ev₂ φ])
        ?_ ?_ (fun X _ => X.elim0) (fun X _ => X.elim0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ φ
      · intro k r v _ _ hc ht
        exact .atom (trueArithLits₂_ev₂ (isArithLit₂_of_numClosed_rel r v hc) ht)
      · intro k r v _ _ hc ht
        exact .atom (trueArithLits₂_ev₂ (isArithLit₂_of_numClosed_nrel r v hc) ht)
      · intro X t _ hS _ _; exact absurd hS (by simp)
      · intro X t _ hS _ _; exact absurd hS (by simp)
      · intro _ _ _ _; rw [ev₂_verum]; exact .verum
      · intro _ _ _ ht; exact absurd ht (by simp [TrueN₂])
      · intro φ' ψ' hcx _ _ _; simp at hcx
      · intro φ' ψ' hcx _ _ _; simp at hcx
      · intro φ' hcx _ _ _; simp at hcx
      · intro φ' hcx _ _ _; simp at hcx
      · intro φ' _ hS _ _; exact absurd hS (by simp)
      · intro φ' _ hS _ _; exact absurd hS (by simp)
  | succ c ih =>
      intro φ
      refine cases₀ (C := fun φ => φ.complexity ≤ c + 1 → SetFree φ → NumClosed φ → TrueN₂ φ →
        OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0
          (OrdinalNotation.ofNat (c + 1)) [ev₂ φ])
        ?_ ?_ (fun X _ => X.elim0) (fun X _ => X.elim0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ φ
      · intro k r v _ _ hc ht
        exact .atom (trueArithLits₂_ev₂ (isArithLit₂_of_numClosed_rel r v hc) ht)
      · intro k r v _ _ hc ht
        exact .atom (trueArithLits₂_ev₂ (isArithLit₂_of_numClosed_nrel r v hc) ht)
      · intro X t _ hS _ _; exact absurd hS (by simp)
      · intro X t _ hS _ _; exact absurd hS (by simp)
      · intro _ _ _ _; rw [ev₂_verum]; exact .verum
      · intro _ _ _ ht; exact absurd ht (by simp [TrueN₂])
      · -- `φ ⋏ ψ`: both conjuncts are true, and both premises are needed.
        intro φ' ψ' hcx hS hc ht
        simp only [Semiformula.complexity_and] at hcx
        simp only [setFree_and] at hS
        simp only [numClosed_and] at hc
        rw [trueN₂_and] at ht
        rw [ev₂_and]
        exact .and (OrdinalNotation.ofNat_lt_ofNat (Nat.lt_succ_self c))
          (OrdinalNotation.ofNat_lt_ofNat (Nat.lt_succ_self c))
          (ih φ' (by omega) hS.1 hc.1 ht.1) (ih ψ' (by omega) hS.2 hc.2 ht.2)
      · -- `φ ⋎ ψ`: one disjunct is true; the other is added by weakening.
        intro φ' ψ' hcx hS hc ht
        simp only [Semiformula.complexity_or] at hcx
        simp only [setFree_or] at hS
        simp only [numClosed_or] at hc
        rw [trueN₂_or] at ht
        rw [ev₂_or]
        refine .or (OrdinalNotation.ofNat_lt_ofNat (Nat.lt_succ_self c)) ?_
        rcases ht with h | h
        · exact .contraction (by simp) (ih φ' (by omega) hS.1 hc.1 h)
        · exact .contraction (by simp) (ih ψ' (by omega) hS.2 hc.2 h)
      · -- `∀¹ φ`: every numeral instance is true, closed and set-free.
        intro φ' hcx hS hc ht
        simp only [Semiformula.complexity_all₁] at hcx
        simp only [setFree_all₁] at hS
        simp only [numClosed_all₁] at hc
        rw [trueN₂_all] at ht
        rw [ev₂_all₁]
        refine .omegaRule (fun _ => OrdinalNotation.ofNat c)
          (fun _ => OrdinalNotation.ofNat_lt_ofNat (Nat.lt_succ_self c)) (fun m => ?_)
        rw [evInst₂_inst_ev]
        exact ih (φ'/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)]) (by simp; omega)
          (by simpa using hS) (numClosed_subst_numAt hc m) (ht m)
      · -- `∃¹ φ`: some numeral instance is true.
        intro φ' hcx hS hc ht
        simp only [Semiformula.complexity_exs₁] at hcx
        simp only [setFree_exs₁] at hS
        simp only [numClosed_exs₁] at hc
        rw [trueN₂_exs] at ht
        rw [ev₂_exs₁]
        obtain ⟨m, hm⟩ := ht
        refine .exs m (OrdinalNotation.ofNat_lt_ofNat (Nat.lt_succ_self c)) ?_
        rw [evInst₂_inst_ev]
        exact ih (φ'/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)]) (by simp; omega)
          (by simpa using hS) (numClosed_subst_numAt hc m) hm
      · intro φ' _ hS _ _; exact absurd hS (by simp)
      · intro φ' _ hS _ _; exact absurd hS (by simp)

/-- **ω-completeness for the set-free fragment.**

Every closed, set-free proposition true in the standard ω-structure has a
cut-free derivation of its own evaluation, at height its own complexity — in
particular at a *finite* height.

This is the master lemma of the `ACA` lower bound: it discharges the equality
axioms, `PA⁻`, and (through `AxiomsInduction₂.lean`) the matrix of every
induction and comprehension instance. -/
theorem omega_complete₂_ev (φ : Proposition ℒₒᵣ) (hS : SetFree φ) (hc : NumClosed φ)
    (ht : TrueN₂ φ) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (hgt₂ φ) [ev₂ φ] :=
  omega_complete₂_aux φ.complexity φ le_rfl hS hc ht

/-- The same at any height above `hgt₂ φ`. -/
theorem omega_complete₂_ev_of_le (φ : Proposition ℒₒᵣ) (hS : SetFree φ)
    (hc : NumClosed φ) (ht : TrueN₂ φ) {α : O} (hα : hgt₂ φ ≤ α) :
    OmegaDerivable₂ trueArithLits₂ evInst₂ 0 α [ev₂ φ] :=
  (omega_complete₂_ev φ hS hc ht).mono_ord hα

/-- **The form at an `ev₂`-fixed formula.**  When the proposition is already in
normal form the conclusion is the proposition itself. -/
theorem omega_complete₂ (φ : Proposition ℒₒᵣ) (hS : SetFree φ) (hc : NumClosed φ)
    (ht : TrueN₂ φ) (hev : ev₂ φ = φ) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (hgt₂ φ) [φ] := by
  have h := omega_complete₂_ev (O := O) φ hS hc ht
  rwa [hev] at h

/-- **The negative form**: a closed set-free proposition *false* in the standard
ω-structure has its negation derived, at the same height. -/
theorem omega_complete₂_ev_neg (φ : Proposition ℒₒᵣ) (hS : SetFree φ)
    (hc : NumClosed φ) (hf : ¬ TrueN₂ φ) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (hgt₂ φ) [ev₂ (∼φ)] := by
  have h := omega_complete₂_ev (O := O) (∼φ) (by simpa using hS) (by simpa using hc)
    ((trueN₂_neg φ).mpr hf)
  simpa using h

/-! ### The form the `𝗘𝗤` and `𝗣𝗔⁻` rows consume -/

/-- Truth of a lifted first-order formula is truth of the original. -/
theorem trueN₂_lift {φ : FirstOrder.Semiformula ℒₒᵣ ℕ 0} :
    TrueN₂ (lift φ : Proposition ℒₒᵣ) ↔
      FirstOrder.Semiformula.Eval (M := ℕ) ![] (fun _ => 0) φ := by
  rw [TrueN₂]
  exact evalSO_lift φ

/-- **A lifted first-order sentence, true in `ℕ`, is derivable at a finite
height.**

Stated with `lift (Rewriting.emb σ)` rather than with `ACA.liftSentence σ` so
that this file does not have to import `ACA/LK.lean`; the two are definitionally
equal, and `AxiomsLogic₂.lean` uses it under the latter name. -/
theorem omega_complete₂_liftEmb (σ : FirstOrder.Sentence ℒₒᵣ)
    (h : FirstOrder.Semiformula.Eval (M := ℕ) ![] Empty.elim σ) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0
        (hgt₂ (lift (FirstOrder.Rewriting.emb σ : FirstOrder.Semiformula ℒₒᵣ ℕ 0) :
          Proposition ℒₒᵣ))
      [ev₂ (lift (FirstOrder.Rewriting.emb σ : FirstOrder.Semiformula ℒₒᵣ ℕ 0) :
        Proposition ℒₒᵣ)] := by
  refine omega_complete₂_ev
    (lift (FirstOrder.Rewriting.emb σ : FirstOrder.Semiformula ℒₒᵣ ℕ 0) : Proposition ℒₒᵣ)
    (setFree_lift _) (numClosed_lift (by simp)) ?_
  rw [trueN₂_lift]
  simpa using h

end OmegaTruth₂

end OrdinalAnalysis.ACAOmega
