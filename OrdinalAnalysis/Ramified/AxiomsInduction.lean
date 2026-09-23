/-
  The induction axioms of `RA Λ`, replayed in the ramified ω-calculus (design
  D2).

  This is `Gentzen/AxiomsInduction.lean` transported from `LX` to `LRA`.  The
  scheme itself is unchanged — `succInd` is `Foundation`'s own,
  language-generic, definition — and the argument does not depend on the
  ramification at all: the induction hypothesis may mention `X` and any
  `∈̇_ν`, but the chain that replaces induction by the ω-rule only ever
  substitutes *numbers* for the bound variable, and level bookkeeping never
  enters. So this file is close to a verbatim port, with two adjustments.

  * **Identity is atomic in `Ramified/Calculus.lean`**, exactly as in
    `Omega/Calculus.lean` (`OmegaDerivableR.identity` only fires on a
    relation/negated-relation pair), unlike `ACAOmega/Calculus.lean`'s general
    `identity`.  The chain's `ψ(n̄), ∼ψ(n̄)` step needs identity for the
    *compound* formula `ψ`, so this file ports `Omega/Identity.lean`'s
    `identity_of_mem`/`identity_general` to `OmegaDerivableR` under the names
    `identityR_of_mem`/`identityR_general` — the exact induction on `φ`, using
    `OmegaDerivableR`'s own `of_mem_identity`/`of_mem_verum`/`or`/`and`/
    `omegaRule`/`exs`/`drop_head`.  A general identity lemma may be of use
    elsewhere in the ramified development; it is kept local to this file
    (under the distinct name `identityR_of_mem`/`identityR_general`) rather
    than factored into a shared file, so that this file has no dependency
    beyond `Ramified/AxiomsLogic.lean`.

  * **The universal closure is peeled by `Ramified/AxiomsLogic.lean`'s
    `allClosureR_derivable`**, not by a bespoke local lemma: the induction
    scheme's closure and `relExt (∈̇_ν)`'s closure are the same shape (a
    `k`-ary matrix, closed by a simultaneous numeral assignment), so this file
    imports `AxiomsLogic.lean` and reuses that lemma directly, saving the
    `allClosure_aux`/`allClosure_derivable` half of the corresponding Gentzen
    file entirely.

  Both blocks land in `OmegaDerivableR trueArithLitsR evInstR`, cut-free
  (rank `0`), at heights in `Gamma0Note` — see `AxiomsLogic.lean`'s header for
  why heights are not stated generically in `[OrdinalNotation O]`
  (`allClosureR_derivable`'s own `nadd β (ofNat k)` bookkeeping, which this
  file's Step 3 needs, is exactly the obstruction).

  Contents.

    `identityR_of_mem`, `identityR_general`
                                     **general identity**, ported from
                                     `Omega/Identity.lean`
    `sucTR`, `zeroTR`                the two closed pieces of `succInd`
    `add_operator_eq_funcR`, `subst_sucTR`, `groundR_subst_sucTR`,
    `evTermR_subst_sucTR`           `(#0 + 1)[n̄]` is ground and denotes `n + 1`
    `subst_substR`, `subst_bvar_substR`
                                     composing substitutions
    `complexity_evR_subst`          evaluating + substituting keeps complexity
    `stepBodyR`, `neg_stepR`        the negated induction step is an `∃`
    `inst_stepBodyR`                **its `n`-th instance is `ψ(n̄) ⋏ ¬ψ(n+1‾)`**
    `chainR_aux`, `chainR`          **Step 1** — the chain, height `2c + 2n`
    `ev_succIndR`, `omegaGR`, `succIndR_derivable`
                                     **Step 2** — the closed axiom, height `ω ⊕ 2`
    `numSubstR₁_subst`, `numSubstR₁_sucTR`, `numSubstR_zeroTR`, `numSubstR_succInd`
                                     a numeral assignment passes through `succInd`
    `induction_axiom_derivable`     **Step 3/4** — every induction axiom of `RA Λ`
-/
import OrdinalAnalysis.Ramified.AxiomsLogic

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

/-! ### General identity, ported from `Omega/Identity.lean`

`Ramified/Calculus.lean`'s `identity` is atomic, exactly as
`Omega/Calculus.lean`'s is; every formula still has a derivation of `φ, ∼φ` by
induction on `φ`, at a finite height, and the proof transfers unchanged to
`OmegaDerivableR` — the calculus's shape (atomic identity, an ω-rule whose
instantiation preserves complexity) is identical, only the ambient inductive
type differs. -/

/-- **Identity, for members.**  A sequent containing a formula of complexity
at most `c` together with its negation is derivable at height `2c`. -/
theorem identityR_of_mem {r : Gamma0Note} :
    ∀ (c : ℕ) (φ : Proposition LRA), φ.complexity ≤ c →
      ∀ {Θ : Sequent LRA}, φ ∈ Θ → ∼φ ∈ Θ →
        OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR r (OrdinalNotation.ofNat (2 * c)) Θ := by
  intro c
  induction c with
  | zero =>
      intro φ hc Θ h₁ h₂
      cases φ with
      | verum => exact OmegaDerivableR.of_mem_verum h₁
      | falsum => exact OmegaDerivableR.of_mem_verum h₂
      | rel rl v => exact OmegaDerivableR.of_mem_identity rl v h₁ h₂
      | nrel rl v => exact OmegaDerivableR.of_mem_identity rl v h₂ h₁
      | and φ ψ => simp at hc
      | or φ ψ => simp at hc
      | all φ => simp at hc
      | exs φ => simp at hc
  | succ c ih =>
      intro φ hc Θ h₁ h₂
      have hlt₁ : (OrdinalNotation.ofNat (2 * c) : Gamma0Note) < OrdinalNotation.ofNat (2 * c + 1) :=
        OrdinalNotation.ofNat_lt_ofNat (by omega)
      have hlt₂ : (OrdinalNotation.ofNat (2 * c + 1) : Gamma0Note) < OrdinalNotation.ofNat (2 * (c + 1)) :=
        OrdinalNotation.ofNat_lt_ofNat (by omega)
      cases φ with
      | verum => exact OmegaDerivableR.of_mem_verum h₁
      | falsum => exact OmegaDerivableR.of_mem_verum h₂
      | rel rl v => exact OmegaDerivableR.of_mem_identity rl v h₁ h₂
      | nrel rl v => exact OmegaDerivableR.of_mem_identity rl v h₂ h₁
      | and φ ψ =>
          simp only [Semiformula.complexity_and'] at hc
          have h₂' : (∼φ ⋎ ∼ψ) ∈ Θ := h₂
          refine OmegaDerivableR.drop_head (OmegaDerivableR.or hlt₂ ?_) h₂'
          refine OmegaDerivableR.drop_head
            (OmegaDerivableR.and (Γ := ∼φ :: ∼ψ :: Θ) hlt₁ hlt₁ ?_ ?_)
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h₁))
          · exact ih φ (by omega) List.mem_cons_self (by simp)
          · exact ih ψ (by omega) List.mem_cons_self (by simp)
      | or φ ψ =>
          simp only [Semiformula.complexity_or'] at hc
          have h₂' : (∼φ ⋏ ∼ψ) ∈ Θ := h₂
          refine OmegaDerivableR.drop_head (OmegaDerivableR.and hlt₂ hlt₂ ?_ ?_) h₂'
          · refine OmegaDerivableR.drop_head
              (OmegaDerivableR.or (Γ := ∼φ :: Θ) hlt₁ ?_) (List.mem_cons_of_mem _ h₁)
            exact ih φ (by omega) List.mem_cons_self (by simp)
          · refine OmegaDerivableR.drop_head
              (OmegaDerivableR.or (Γ := ∼ψ :: Θ) hlt₁ ?_) (List.mem_cons_of_mem _ h₁)
            exact ih ψ (by omega) (by simp) (by simp)
      | all φ =>
          simp only [Semiformula.complexity_all'] at hc
          have h₂' : (∃¹ ∼φ) ∈ Θ := h₂
          refine OmegaDerivableR.drop_head (OmegaDerivableR.omegaRule (Γ := Θ)
            (fun _ => OrdinalNotation.ofNat (2 * c + 1)) (fun _ => hlt₂) (fun n => ?_)) h₁
          refine OmegaDerivableR.drop_head
            (OmegaDerivableR.exs (Γ := evInstR.inst φ n :: Θ) n hlt₁ ?_)
            (List.mem_cons_of_mem _ h₂')
          rw [InstantiationR.inst_neg]
          exact ih (evInstR.inst φ n)
            (by have h : (evInstR.inst φ n).complexity = φ.complexity := Instantiation.complexity_inst evInstR.toInstantiation φ n; omega)
            (by simp) List.mem_cons_self
      | exs φ =>
          simp only [Semiformula.complexity_exs'] at hc
          have h₂' : (∀¹ ∼φ) ∈ Θ := h₂
          refine OmegaDerivableR.drop_head (OmegaDerivableR.omegaRule (Γ := Θ)
            (fun _ => OrdinalNotation.ofNat (2 * c + 1)) (fun _ => hlt₂) (fun n => ?_)) h₂'
          rw [InstantiationR.inst_neg]
          refine OmegaDerivableR.drop_head
            (OmegaDerivableR.exs (Γ := ∼evInstR.inst φ n :: Θ) n hlt₁ ?_)
            (List.mem_cons_of_mem _ h₁)
          exact ih (evInstR.inst φ n)
            (by have h : (evInstR.inst φ n).complexity = φ.complexity := Instantiation.complexity_inst evInstR.toInstantiation φ n; omega)
            List.mem_cons_self (by simp)

/-- **Identity.** -/
theorem identityR_general {r : Gamma0Note} (φ : Proposition LRA) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR r
      (OrdinalNotation.ofNat (2 * φ.complexity)) [φ, ∼φ] :=
  identityR_of_mem φ.complexity φ le_rfl (by simp) (by simp)

/-! ### The two closed pieces of `succInd` -/

/-- The successor term `#0 + 1` at level `1`. -/
def sucTR : Semiterm LRA ℕ 1 := ‘(#0 + 1)’

/-- The constant `0` as it occurs in `succInd`. -/
def zeroTR : SyntacticTerm LRA := ((0 : ℕ) : SyntacticTerm LRA)

theorem zeroTR_eq : zeroTR = num 0 := by simp [zeroTR, num]

/-- `+` in operator form is `+` in function form. -/
theorem add_operator_eq_funcR {n : ℕ} (a b : Semiterm LRA ℕ n) :
    Semiterm.Operator.Add.add.operator ![a, b]
      = Semiterm.func (Language.Add.add : LRA.Func 2) ![a, b] := by
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func]
  exact congrArg (Semiterm.func (Language.Add.add : LRA.Func 2))
    (by funext i; fin_cases i <;> simp)

/-- The successor term with a numeral substituted. -/
theorem subst_sucTR (n : ℕ) :
    Rew.subst ![(num n : SyntacticTerm LRA)] sucTR
      = Semiterm.func (Language.Add.add : LRA.Func 2) ![num n, num 1] := by
  rw [← add_operator_eq_funcR]
  simp [sucTR, num]

theorem groundR_subst_sucTR (n : ℕ) : GroundR (Rew.subst ![(num n : SyntacticTerm LRA)] sucTR) := by
  rw [subst_sucTR]
  refine (groundR_func_iff _ _).mpr fun i => ?_
  fin_cases i <;> simp

theorem evTermR_subst_sucTR (n : ℕ) :
    evTermR (Rew.subst ![(num n : SyntacticTerm LRA)] sucTR) = n + 1 := by
  rw [subst_sucTR, evTermR_func]
  have h : (fun i => evTermR ((![num n, num 1] : Fin 2 → SyntacticTerm LRA) i)) = ![n, 1] := by
    funext i; fin_cases i <;> simp
  rw [h]
  rfl

/-! ### Composing substitutions -/

/-- Substituting into a substitution instance is a single substitution. -/
theorem subst_substR {n : ℕ} (ψ : Semiformula LRA ℕ 1) (s : Semiterm LRA ℕ 1)
    (t : Semiterm LRA ℕ n) :
    Rew.subst ![t] ▹ (ψ/[s]) = ψ/[Rew.subst ![t] s] := by
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]

theorem subst_bvar_substR {n : ℕ} (ψ : Semiformula LRA ℕ 1) (t : Semiterm LRA ℕ n) :
    Rew.subst ![t] ▹ (ψ/[(#0 : Semiterm LRA ℕ 1)]) = ψ/[t] := by
  rw [subst_substR]; simp

/-- The complexity of an evaluated instance is that of the body. -/
theorem complexity_evR_subst (ψ : Semiproposition LRA 1) (t : SyntacticTerm LRA) :
    (evR (ψ/[t])).complexity = ψ.complexity := by
  rw [complexity_evR, Semiformula.complexity_rew]

/-! ### The chain -/

/-- The body of the existential that the negated induction step is. -/
def stepBodyR (ψ : Semiproposition LRA 1) : Semiproposition LRA 1 :=
  evR (ψ/[(#0 : Semiterm LRA ℕ 1)]) ⋏ ∼evR (ψ/[sucTR])

/-- The negation of the (evaluated) induction step, in the shape the `exs`
rule of the calculus takes. -/
theorem neg_stepR (ψ : Semiproposition LRA 1) :
    ∼evR (∀¹ (ψ/[(#0 : Semiterm LRA ℕ 1)] 🡒 ψ/[sucTR])) = ∃¹ stepBodyR ψ := by
  simp [stepBodyR, Semiformula.imp_eq]

/-- **The instance computation.**  This is where the `n̄ + 1` of the syntax
and the `(n+1)‾` of the ω-rule are reconciled: the evaluator absorbs the
difference. -/
theorem inst_stepBodyR (ψ : Semiproposition LRA 1) (n : ℕ) :
    evInstR.inst (stepBodyR ψ) n
      = evR (ψ/[(num n : SyntacticTerm LRA)]) ⋏ ∼evR (ψ/[(num (n + 1) : SyntacticTerm LRA)]) := by
  have hA : evR ((evR (ψ/[(#0 : Semiterm LRA ℕ 1)]))/[(num n : SyntacticTerm LRA)])
      = evR (ψ/[(num n : SyntacticTerm LRA)]) := by
    rw [evR_rew_evR (ψ/[(#0 : Semiterm LRA ℕ 1)]) 0 (Rew.subst ![(num n : SyntacticTerm LRA)])]
    exact congrArg evR (subst_bvar_substR ψ (num n))
  have hB : evR ((evR (ψ/[sucTR]))/[(num n : SyntacticTerm LRA)])
      = evR (ψ/[(num (n + 1) : SyntacticTerm LRA)]) := by
    rw [evR_rew_evR (ψ/[sucTR]) 0 (Rew.subst ![(num n : SyntacticTerm LRA)])]
    have h1 : Rew.subst ![(num n : SyntacticTerm LRA)] ▹ (ψ/[sucTR])
        = ψ/[Rew.subst ![(num n : SyntacticTerm LRA)] sucTR] := subst_substR ψ sucTR (num n)
    rw [h1, evR_subst_ground (groundR_subst_sucTR n) ψ, evTermR_subst_sucTR]
  rw [evInstR_inst, stepBodyR]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg,
    evR_and, evR_neg, hA, hB]

/-- **Step 1, in membership form.**  From `¬ψ(0̄)`, the negated induction step
and `ψ(n̄)` in the sequent, a cut-free derivation of height `2·complexity +
2n`. -/
theorem chainR_aux (ψ : Semiproposition LRA 1) :
    ∀ (n : ℕ) (Γ : Sequent LRA), ∼evR (ψ/[zeroTR]) ∈ Γ → (∃¹ stepBodyR ψ) ∈ Γ →
      evR (ψ/[(num n : SyntacticTerm LRA)]) ∈ Γ →
      OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
        (OrdinalNotation.ofNat (2 * ψ.complexity + 2 * n)) Γ := by
  intro n
  induction n with
  | zero =>
      intro Γ hZ _ hP
      have harith : 2 * ψ.complexity + 2 * 0 = 2 * ψ.complexity := by omega
      rw [harith]
      refine identityR_of_mem ψ.complexity (evR (ψ/[(num 0 : SyntacticTerm LRA)]))
        (le_of_eq (complexity_evR_subst ψ (num 0))) hP ?_
      rw [← zeroTR_eq]
      exact hZ
  | succ n ih =>
      intro Γ hZ hS hP
      have hlt₁ : (OrdinalNotation.ofNat (2 * ψ.complexity + 2 * n) : Gamma0Note)
          < OrdinalNotation.ofNat (2 * ψ.complexity + 2 * n + 1) :=
        OrdinalNotation.ofNat_lt_ofNat (by omega)
      have hlt₂ : (OrdinalNotation.ofNat (2 * ψ.complexity) : Gamma0Note)
          < OrdinalNotation.ofNat (2 * ψ.complexity + 2 * n + 1) :=
        OrdinalNotation.ofNat_lt_ofNat (by omega)
      have hlt₃ : (OrdinalNotation.ofNat (2 * ψ.complexity + 2 * n + 1) : Gamma0Note)
          < OrdinalNotation.ofNat (2 * ψ.complexity + 2 * (n + 1)) :=
        OrdinalNotation.ofNat_lt_ofNat (by omega)
      have d₁ : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
          (OrdinalNotation.ofNat (2 * ψ.complexity + 2 * n))
          (evR (ψ/[(num n : SyntacticTerm LRA)]) :: Γ) :=
        ih _ (List.mem_cons_of_mem _ hZ) (List.mem_cons_of_mem _ hS) List.mem_cons_self
      have d₂ : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
          (OrdinalNotation.ofNat (2 * ψ.complexity))
          (∼evR (ψ/[(num (n + 1) : SyntacticTerm LRA)]) :: Γ) :=
        identityR_of_mem ψ.complexity (evR (ψ/[(num (n + 1) : SyntacticTerm LRA)]))
          (le_of_eq (complexity_evR_subst ψ (num (n + 1))))
          (List.mem_cons_of_mem _ hP) List.mem_cons_self
      have d₃ : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
          (OrdinalNotation.ofNat (2 * ψ.complexity + 2 * n + 1))
          (evInstR.inst (stepBodyR ψ) n :: Γ) := by
        rw [inst_stepBodyR]
        exact OmegaDerivableR.and hlt₁ hlt₂ d₁ d₂
      exact OmegaDerivableR.drop_head (OmegaDerivableR.exs n hlt₃ d₃) hS

/-- **Step 1.**  The chain, as a three-element sequent. -/
theorem chainR (ψ : Semiproposition LRA 1) (n : ℕ) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
      (OrdinalNotation.ofNat (2 * ψ.complexity + 2 * n))
      [∼evR (ψ/[zeroTR]), ∼evR (∀¹ (ψ/[(#0 : Semiterm LRA ℕ 1)] 🡒 ψ/[sucTR])),
       evR (ψ/[(num n : SyntacticTerm LRA)])] :=
  chainR_aux ψ n _ (by simp) (by rw [← neg_stepR]; simp) (by simp)

/-! ### Step 2: the closed induction axiom -/

/-- `succInd φ` unfolds definitionally to the three substitution instances
joined by `→` and `∀¹`. -/
theorem succInd_eqR (φ : Semiformula LRA ℕ 1) :
    succInd φ = (φ/[(zeroTR : SyntacticTerm LRA)]) 🡒
      (∀¹ (φ/[(#0 : Semiterm LRA ℕ 1)] 🡒 φ/[sucTR])) 🡒 ∀¹ (φ/[(#0 : Semiterm LRA ℕ 1)]) := rfl

/-- `evR` of an induction axiom, in the shape the two `or` rules produce. -/
theorem ev_succIndR (ψ : Semiproposition LRA 1) :
    evR (succInd ψ)
      = ∼evR (ψ/[zeroTR]) ⋎ (∼evR (∀¹ (ψ/[(#0 : Semiterm LRA ℕ 1)] 🡒 ψ/[sucTR]))
          ⋎ (∀¹ (evR (ψ/[(#0 : Semiterm LRA ℕ 1)])))) := by
  rw [succInd_eqR]
  simp [Semiformula.imp_eq]

/-- `ω`, as a `Gamma0Note`. -/
def omegaGR : Gamma0Note := Gamma0Note.omegaPow 1

theorem ofNat_lt_omegaGR (n : ℕ) : (OrdinalNotation.ofNat n : Gamma0Note) < omegaGR := by
  show Gamma0Note.ofNat n < omegaGR
  rw [Gamma0Note.lt_def, Gamma0Note.repr_ofNat, omegaGR, Gamma0Note.repr_omegaPow,
    Gamma0Note.repr_one, Ordinal.opow_one]
  exact Ordinal.natCast_lt_omega0 n

theorem lt_nadd_oneR {a : Gamma0Note} : a < OrdinalNotation.nadd a (OrdinalNotation.ofNat 1) := by
  have h := OrdinalNotation.nadd_lt_nadd_right (a := a) (OrdinalNotation.ofNat_lt_ofNat
    (show (0 : ℕ) < 1 by omega))
  rw [ofNat_zero_R] at h
  simpa using h

theorem lt_nadd_ofNatR {a : Gamma0Note} {j k : ℕ} (h : j < k) :
    OrdinalNotation.nadd a (OrdinalNotation.ofNat j) < OrdinalNotation.nadd a (OrdinalNotation.ofNat k) :=
  OrdinalNotation.nadd_lt_nadd_right a (OrdinalNotation.ofNat_lt_ofNat h)

/-- **Step 2.**  Every induction axiom with a *closed* body is derivable,
cut-free, at height `ω ⊕ 2`. -/
theorem succIndR_derivable (ψ : Semiproposition LRA 1) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
      (OrdinalNotation.nadd omegaGR (OrdinalNotation.ofNat 2)) [evR (succInd ψ)] := by
  have h1 : omegaGR < OrdinalNotation.nadd omegaGR (OrdinalNotation.ofNat 1) := lt_nadd_oneR
  have h2 : OrdinalNotation.nadd omegaGR (OrdinalNotation.ofNat 1)
      < OrdinalNotation.nadd omegaGR (OrdinalNotation.ofNat 2) := lt_nadd_ofNatR (by omega)
  have hinst : ∀ n : ℕ, evInstR.inst (evR (ψ/[(#0 : Semiterm LRA ℕ 1)])) n
      = evR (ψ/[(num n : SyntacticTerm LRA)]) := by
    intro n
    rw [evInstR_inst_ev]
    exact congrArg evR (subst_bvar_substR ψ (num n))
  have dω : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 omegaGR
      ((∀¹ (evR (ψ/[(#0 : Semiterm LRA ℕ 1)])))
        :: [∼evR (ψ/[zeroTR]), ∼evR (∀¹ (ψ/[(#0 : Semiterm LRA ℕ 1)] 🡒 ψ/[sucTR]))]) := by
    refine OmegaDerivableR.omegaRule
      (fun n => OrdinalNotation.ofNat (2 * ψ.complexity + 2 * n)) (fun n => ofNat_lt_omegaGR _)
      (fun n => ?_)
    rw [hinst n]
    exact OmegaDerivableR.contraction (by intro x hx; simp at hx ⊢; tauto) (chainR ψ n)
  have d₁ : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
      (OrdinalNotation.nadd omegaGR (OrdinalNotation.ofNat 1))
      [∼evR (∀¹ (ψ/[(#0 : Semiterm LRA ℕ 1)] 🡒 ψ/[sucTR])) ⋎ (∀¹ (evR (ψ/[(#0 : Semiterm LRA ℕ 1)]))),
       ∼evR (ψ/[zeroTR])] :=
    OmegaDerivableR.or h1 (OmegaDerivableR.contraction (by intro x hx; simp at hx ⊢; tauto) dω)
  have d₂ : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
      (OrdinalNotation.nadd omegaGR (OrdinalNotation.ofNat 2))
      [∼evR (ψ/[zeroTR]) ⋎ (∼evR (∀¹ (ψ/[(#0 : Semiterm LRA ℕ 1)] 🡒 ψ/[sucTR]))
        ⋎ (∀¹ (evR (ψ/[(#0 : Semiterm LRA ℕ 1)]))))] :=
    OmegaDerivableR.or h2 (OmegaDerivableR.contraction (by intro x hx; simp at hx ⊢; tauto) d₁)
  rw [ev_succIndR]
  exact d₂

/-! ### Step 3: peeling the universal closure and passing a numeral
assignment through `succInd`

`Ramified/AxiomsLogic.lean`'s `allClosureR_derivable` does the peeling; what
remains is to identify the fully-instantiated matrix with `succInd` applied to
a numeral-substituted body, exactly as `Gentzen/AxiomsInduction.lean`'s
`numSubst_succInd` does for `numSubst`/`numSubst₁`. -/

theorem numSubstR₁_subst (a : ℕ → ℕ) (s : Semiterm LRA ℕ 1) (φ : Semiformula LRA ℕ 1) :
    numSubstR₁ a ▹ (φ/[s]) = (numSubstR₁ a ▹ φ)/[numSubstR₁ a s] := by
  simpa [← comp_app] using smul_ext' (φ := φ) <| by ext x <;> simp [Rew.comp_app, numSubstR₁]

theorem numSubstR₁_sucTR (a : ℕ → ℕ) : numSubstR₁ a sucTR = sucTR := by
  simp [sucTR, numSubstR₁]

theorem numSubstR_zeroTR (a : ℕ → ℕ) : numSubstR a zeroTR = zeroTR := by
  simp [zeroTR, numSubstR]

@[simp] theorem numSubstR_q (a : ℕ → ℕ) : (numSubstR a).q = numSubstR₁ a := by
  simp only [numSubstR, numSubstR₁]
  ext x <;> simp [num]

/-- **A numeral assignment passes through an induction axiom**: the three
occurrences of the body are all substituted, and the closed terms `0̄`, `#0`
and `#0 + 1` are all fixed. -/
theorem numSubstR_succInd (a : ℕ → ℕ) (φ : Semiproposition LRA 1) :
    numSubstR a ▹ succInd φ = succInd (numSubstR₁ a ▹ φ) := by
  show numSubstR a ▹ ((φ/[zeroTR])
      🡒 (∀¹ (φ/[(#0 : Semiterm LRA ℕ 1)] 🡒 φ/[sucTR]))
      🡒 ∀¹ (φ/[(#0 : Semiterm LRA ℕ 1)]))
    = ((numSubstR₁ a ▹ φ)/[zeroTR])
      🡒 (∀¹ ((numSubstR₁ a ▹ φ)/[(#0 : Semiterm LRA ℕ 1)]
            🡒 (numSubstR₁ a ▹ φ)/[sucTR]))
      🡒 ∀¹ ((numSubstR₁ a ▹ φ)/[(#0 : Semiterm LRA ℕ 1)])
  simp [Semiformula.imp_eq, numSubstR_subst, numSubstR_zeroTR, numSubstR₁_subst, numSubstR₁_sucTR]

/-! ### Step 4: the induction axioms of `RA Λ` -/

/-- **Every axiom of the induction scheme of `RA Λ` has a cut-free derivation
in the ω-calculus.**  The side condition on the scheme (which formulas it
ranges over) is irrelevant to the derivation itself — it is uniform in `φ` —
and only restricts which instances a given `RAlt ν` actually contains. -/
theorem induction_axiom_derivable {Γ : Semiformula LRA ℕ 1 → Prop}
    {σ : Sentence LRA} (h : σ ∈ InductionScheme LRA Γ) :
    ∃ β : Gamma0Note, OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb σ : Proposition LRA)] := by
  obtain ⟨φ, -, rfl⟩ := h
  refine ⟨OrdinalNotation.nadd (OrdinalNotation.nadd omegaGR (OrdinalNotation.ofNat 2))
      (OrdinalNotation.ofNat (0 + (succInd φ).fvSup)), ?_⟩
  have hemb : (Rewriting.emb (Semiformula.univCl (succInd φ)) : Proposition LRA)
      = ∀¹* (Rew.fixitr 0 (succInd φ).fvSup ▹ (succInd φ)) := by
    simp [Semiformula.univCl']
  rw [hemb]
  refine allClosureR_derivable (Rew.fixitr 0 (succInd φ).fvSup ▹ (succInd φ)) (fun w => ?_)
  have key : (Rew.fixitr 0 (succInd φ).fvSup ▹ (succInd φ))
        ⇜ (fun i : Fin (0 + (succInd φ).fvSup) => (numAtR (w i) : SyntacticTerm LRA))
      = Rew.rewrite (fun y => (numAtR (if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0)
          : SyntacticTerm LRA)) ▹ (succInd φ) := by
    have hvec : (fun i : Fin (0 + (succInd φ).fvSup) => (numAtR (w i) : SyntacticTerm LRA))
        = (fun i : Fin (0 + (succInd φ).fvSup) =>
            (fun y => (numAtR (if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0)
              : SyntacticTerm LRA)) (i : ℕ)) := by
      funext i
      simp only [dif_pos i.isLt, Fin.eta]
    rw [hvec]
    exact Semiformula.subst_comp_fixitr_eq_map (succInd φ)
      (fun y => (numAtR (if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0) : SyntacticTerm LRA))
  have hns : Rew.rewrite
        (fun y => (numAtR (if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0) : SyntacticTerm LRA))
      = numSubstR (fun y => if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0) := rfl
  rw [key, hns, numSubstR_succInd]
  exact succIndR_derivable _

end Ramified

end OrdinalAnalysis
