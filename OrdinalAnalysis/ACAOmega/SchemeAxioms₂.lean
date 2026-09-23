/-
  The two *schema* blocks of `ACA` — the induction scheme `indScheme₂ φ` and
  arithmetical comprehension `arithComp₂ ψ` — replayed in the evaluating
  ω-calculus.

  `ACAOmega/AxiomsInduction₂.lean` delivered every **structural** ingredient:
  `allN₂_derivable` peels the `∀²`-prefix, `allN₁_derivable` peels the
  `∀¹`-prefix, `freeN₁_allN₁` says the two prefixes may be peeled
  independently, `succInd₂_derivable` derives the induction axiom for an
  arbitrary one-variable body and `iff_self_derivable` the comprehension leaf.
  What was missing — and is supplied here — is the **instantiation
  computation**: the identification of the fully freed, fully instantiated body
  with the shape those two leaves consume.

  ### The induction scheme

  Two steps.  First, `free₁` (a *set*-variable rewriting whose `bv`/`fv` are
  atoms) slides straight through `indBody`, because `indBody` is built from
  `⋏`/`🡒`/`∀¹` and two first-order substitutions and
  `SecondOrder.Rew.app_comm_subst` moves a set rewriting across any of those:
  `freeN₁ M (indBody φ) = indBody (freeN₁ M φ)`.  Second, substituting a vector
  of numerals into `indBody` turns it into `succInd₂` of the substituted body:

      Rew.subst w ▹ indBody φ = succInd₂ ((Rew.subst w).q ▹ φ)

  which rests on the two composite-`Rew` identities

      (Rew.subst w).comp (Rew.subst (indZeroSub n))
        = (Rew.subst ![zeroT]).comp (Rew.subst w).q
      (Rew.subst w).q.comp (Rew.subst (indSuccSub n))
        = (Rew.subst ![succT]).comp (Rew.subst w).q

  — both sides send `#0 ↦ 0` (resp. `#0 + 1`), `#(i+1) ↦ w i` and `&x ↦ &x`,
  so both are `FirstOrder.Rew.ext` plus `Fin.cases`.

  ### Comprehension

  The one computation that looks genuinely fiddly is the
  `(∃₂)` witness.  It is not fiddly once the right lemma is isolated.
  `compBody ψ = ∃² (∀¹ ((#0 ∈# 0) 🡘 ψ.bmap Fin.succ))` pushes `ψ`'s own set
  parameters up by one so that the comprehended set `Y` can take slot `0`.  Now
  `Semiproposition.free₁` frees the **last** set slot, so freeing `ψ`'s `N`
  parameters out of `ψ.bmap Fin.succ` leaves slot `0` — `Y`'s slot — untouched:

      freeN₁' M (χ.bmap Fin.succ) = (freeN₁ M χ).bmap Fin.succ     (Fin 0 → Fin 1)

  whose inductive step is exactly `Rew.free.bRight Fin.succ =
  Rew.free.bLeft Fin.succ`, "freeing the last slot commutes with pushing every
  slot up by one".  With that, the body of the comprehension instance is a
  `bmap` from `Fin 0`, the witness is the very formula underneath it, and
  substituting it back is the identity (`subst₂_bmap_succ`, via
  `Rew.subst ![C] |>.bRight (Fin.succ : Fin 0 → Fin 1) = Rew.id`).  The instance
  is then `∀¹ (C 🡘 C)`, closed by `iff_self_derivable` under one ω-rule.

  ### The heights

  Every height certified here is below **`ε₀`**, not merely below `ε_{ε₀}`.
  That is what the assembly in `LowerBound₂.lean` needs: the second cut
  elimination sends a derivation of height `α` and rank `ω + k` to one of height
  `ε_{ω_k(α)}`, and `ε_{ω_k(α)} < ε_{ε₀}` requires `ω_k(α) < ε₀`, hence
  `α < ε₀`.  The schema heights are `((ω ⊕ 2) ⊕ n) ⊕ N` (induction) and
  `(4 ⊕ n) ⊕ N` (comprehension), and `ε₀` is closed under `⊕` and `ω ^ ·`.
  The `< ε_{ε₀}` forms are the immediate corollaries.
-/
import OrdinalAnalysis.ACAOmega.Axioms₂

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA
open OrdinalAnalysis.ACAOmega.OmegaTruth₂
open OrdinalAnalysis.ACAOmega.AxiomsLogic₂
open OrdinalAnalysis.ACAOmega.AxiomsInduction₂
open OrdinalAnalysis.ACAOmega.Axioms₂

namespace SchemeAxioms₂

/-! ### `ε₀`, and the heights below it

The bound every axiom's height has to respect; see the module docstring. -/

/-- `ε₀`, as a `Gamma0Note`. -/
def epsZero : Gamma0Note := Gamma0Note.epsilonNote 0

theorem ofNat_lt_epsZero (n : ℕ) : (OrdinalNotation.ofNat n : Gamma0Note) < epsZero :=
  Gamma0Note.ofNat_lt_epsilon n 0

theorem omegaG_lt_epsZero : omegaG < epsZero :=
  Gamma0Note.omegaPow_lt_epsilon (Gamma0Note.one_lt_epsilon 0)

theorem nadd_lt_epsZero {x y : Gamma0Note} (hx : x < epsZero) (hy : y < epsZero) :
    OrdinalNotation.nadd x y < epsZero :=
  Gamma0Note.nadd_lt_epsilon hx hy

theorem one_lt_epsZero : (OrdinalNotation.one : Gamma0Note) < epsZero :=
  Gamma0Note.one_lt_epsilon 0

theorem succ_lt_epsZero {x : Gamma0Note} (hx : x < epsZero) :
    OrdinalNotation.succ x < epsZero :=
  nadd_lt_epsZero hx one_lt_epsZero

/-- `ε₀ < ε_{ε₀}`: the two bounds of the analysis, in their only relation. -/
theorem epsZero_lt_epsEps : epsZero < epsEps :=
  Gamma0Note.epsilon_lt_epsilon (Gamma0Note.epsilon_pos 0)

/-! ### `free₁` slides through `indBody` -/

/-- **`free₁` commutes with a first-order simultaneous substitution.**  A
set-variable rewriting and a number-variable one never see each other. -/
theorem free₁_subst {N n₁ n₂ : ℕ} (v : Fin n₁ → FirstOrder.Semiterm ℒₒᵣ ℕ n₂)
    (φ : Semiproposition ℒₒᵣ (N + 1) n₁) :
    Semiproposition.free₁ (FirstOrder.Rew.subst v ▹ φ)
      = FirstOrder.Rew.subst v ▹ (Semiproposition.free₁ φ) :=
  SecondOrder.Rew.app_comm_subst _ _ _

theorem free₁_indBody {N n : ℕ} (φ : Semiproposition ℒₒᵣ (N + 1) (n + 1)) :
    Semiproposition.free₁ (indBody φ) = indBody (Semiproposition.free₁ φ) := by
  simp [indBody, LogicalConnective.DeMorgan.imply, free₁_subst]

/-- **Freeing every set parameter slides through `indBody`.** -/
theorem freeN₁_indBody {n : ℕ} : ∀ (M : ℕ) (φ : Semiproposition ℒₒᵣ M (n + 1)),
    freeN₁ M (indBody φ) = indBody (freeN₁ M φ)
  | 0, _ => rfl
  | M + 1, φ => by
      rw [freeN₁_succ, free₁_indBody, freeN₁_indBody M (Semiproposition.free₁ φ), freeN₁_succ]

/-! ### The instantiation computation for the induction scheme -/

section Inst

variable {n : ℕ} (w : Fin n → ℕ)

/-- Both sides send `#0 ↦ 0̄`, `#(i+1) ↦ w i` and `&x ↦ &x`. -/
theorem comp_indZeroSub :
    (FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).comp
        (FirstOrder.Rew.subst (indZeroSub n))
      = (FirstOrder.Rew.subst ![(zeroT : FirstOrder.SyntacticTerm ℒₒᵣ)]).comp
        (FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q := by
  ext x
  · cases x using Fin.cases with
    | zero => simp [FirstOrder.Rew.comp_app, indZeroSub, zeroT]
    | succ i => simp [FirstOrder.Rew.comp_app, indZeroSub]
  · simp [FirstOrder.Rew.comp_app]

/-- Both sides send `#0 ↦ #0 + 1`, `#(i+1) ↦ w i` and `&x ↦ &x`. -/
theorem comp_indSuccSub :
    ((FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q).comp
        (FirstOrder.Rew.subst (indSuccSub n))
      = (FirstOrder.Rew.subst ![(succT : FirstOrder.Semiterm ℒₒᵣ ℕ 1)]).comp
        (FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q := by
  ext x
  · cases x using Fin.cases with
    | zero => simp [FirstOrder.Rew.comp_app, indSuccSub, succT]
    | succ i => simp [FirstOrder.Rew.comp_app, indSuccSub]
  · simp [FirstOrder.Rew.comp_app]

/-- `succInd₂ ψ` with the two inert `ψ/[#0]`s already collapsed. -/
theorem succInd₂_eq (ψ : Semiproposition ℒₒᵣ 0 1) :
    succInd₂ ψ = ((ψ/[(zeroT : FirstOrder.SyntacticTerm ℒₒᵣ)]) ⋏
      (∀¹ (ψ 🡒 ψ/[(succT : FirstOrder.Semiterm ℒₒᵣ ℕ 1)]))) 🡒 ∀¹ ψ := by
  rw [succInd₂, subst_bvar_self]

/-- **The instantiation computation for the induction scheme.** -/
theorem subst_indBody (φ : Semiproposition ℒₒᵣ 0 (n + 1)) :
    FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ)) ▹ (indBody φ)
      = succInd₂ ((FirstOrder.Rew.subst
          (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q ▹ φ) := by
  have eZ : FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))
        ▹ (FirstOrder.Rew.subst (indZeroSub n) ▹ φ)
      = ((FirstOrder.Rew.subst
          (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q ▹ φ)/[
            (zeroT : FirstOrder.SyntacticTerm ℒₒᵣ)] := by
    show _ = FirstOrder.Rew.subst ![(zeroT : FirstOrder.SyntacticTerm ℒₒᵣ)] ▹
      ((FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q ▹ φ)
    rw [← FirstOrder.TransitiveRewriting.comp_app, ← FirstOrder.TransitiveRewriting.comp_app,
      comp_indZeroSub]
  have eS : (FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q
        ▹ (FirstOrder.Rew.subst (indSuccSub n) ▹ φ)
      = ((FirstOrder.Rew.subst
          (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q ▹ φ)/[
            (succT : FirstOrder.Semiterm ℒₒᵣ ℕ 1)] := by
    show _ = FirstOrder.Rew.subst ![(succT : FirstOrder.Semiterm ℒₒᵣ ℕ 1)] ▹
      ((FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q ▹ φ)
    rw [← FirstOrder.TransitiveRewriting.comp_app, ← FirstOrder.TransitiveRewriting.comp_app,
      comp_indSuccSub]
  rw [succInd₂_eq]
  simp only [indBody, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, Semiformula.rew_all₀, eZ, eS]

end Inst

/-! ### The induction scheme is cut-free derivable below `ε₀` -/

/-- **Every instance of the induction scheme of `ACA` is cut-free derivable at a
height below `ε₀`** — at `((ω ⊕ 2) ⊕ n) ⊕ N`, with `n` the number of number
parameters and `N` the number of set parameters. -/
theorem indScheme₂_derivable_lt_eps₀ {N n : ℕ} (φ : Semiproposition ℒₒᵣ N (n + 1)) :
    ∃ β : Gamma0Note, β < epsZero ∧
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ (indScheme₂ φ)] := by
  have hbody : ∀ w : Fin n → ℕ, OmegaDerivable₂ trueArithLits₂ evInst₂ 0
      (OrdinalNotation.nadd omegaG (OrdinalNotation.ofNat 2))
      [ev₂ (FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))
        ▹ (freeN₁ N (indBody φ)))] := by
    intro w
    rw [freeN₁_indBody, subst_indBody]
    exact succInd₂_derivable _
  have h1 := allN₁_derivable (freeN₁ N (indBody φ)) hbody
  rw [← freeN₁_allN₁] at h1
  have h2 := allN₂_derivable (allN₁ n (indBody φ)) h1
  rw [allN₁_eq_allNums, allN₂_eq_allSets] at h2
  refine ⟨_, ?_, h2⟩
  exact nadd_lt_epsZero (nadd_lt_epsZero (nadd_lt_epsZero omegaG_lt_epsZero
    (ofNat_lt_epsZero 2)) (ofNat_lt_epsZero n)) (ofNat_lt_epsZero N)

/-- The scheme form. -/
theorem indScheme₂_derivable {N n : ℕ} (φ : Semiproposition ℒₒᵣ N (n + 1)) :
    ∃ β : Gamma0Note, β < epsEps ∧
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ (indScheme₂ φ)] :=
  let ⟨β, hβ, hd⟩ := indScheme₂_derivable_lt_eps₀ φ
  ⟨β, lt_trans hβ epsZero_lt_epsEps, hd⟩

/-! ### Freeing the set parameters out of `compBody`

`freeN₁'` — `free₁` iterated one set binder short — is the operation the
`∃²`-head forces on us, exactly as it does for the `∀²`-head in
`AxiomsInduction₂.lean`. -/

theorem free₁_exs₂ {M n : ℕ} (φ : Semiproposition ℒₒᵣ (M + 2) n) :
    Semiproposition.free₁ (∃² φ : Semiproposition ℒₒᵣ (M + 1) n)
      = ∃² (Semiproposition.free₁ φ) := by
  show SecondOrder.Rew.free.app (∃² φ) = ∃² (SecondOrder.Rew.free.app φ)
  rw [SecondOrder.Rew.app_exs₁, SecondOrder.Rew.q_free]

theorem freeN₁_exs₂ {n : ℕ} : ∀ (M : ℕ) (φ : Semiproposition ℒₒᵣ (M + 1) n),
    freeN₁ M (∃² φ) = ∃² (freeN₁' M φ)
  | 0, _ => rfl
  | M + 1, φ => by
      rw [freeN₁_succ, free₁_exs₂, freeN₁_exs₂ M (Semiproposition.free₁ φ), freeN₁'_succ]

theorem freeN₁'_all₁ {n : ℕ} : ∀ (M : ℕ) (φ : Semiproposition ℒₒᵣ (M + 1) (n + 1)),
    freeN₁' M (∀¹ φ) = ∀¹ (freeN₁' M φ)
  | 0, _ => rfl
  | M + 1, φ => by
      rw [freeN₁'_succ, free₁_all₁, freeN₁'_all₁ M (Semiproposition.free₁ φ), freeN₁'_succ]

theorem free₁_iff {N n : ℕ} (A B : Semiproposition ℒₒᵣ (N + 1) n) :
    Semiproposition.free₁ (A 🡘 B)
      = Semiproposition.free₁ A 🡘 Semiproposition.free₁ B := by
  simp [LogicalConnective.iff, LogicalConnective.DeMorgan.imply]

theorem freeN₁'_iff {n : ℕ} : ∀ (M : ℕ) (A B : Semiproposition ℒₒᵣ (M + 1) n),
    freeN₁' M (A 🡘 B) = freeN₁' M A 🡘 freeN₁' M B
  | 0, _, _ => rfl
  | M + 1, A, B => by
      rw [freeN₁'_succ, free₁_iff, freeN₁'_iff M, freeN₁'_succ, freeN₁'_succ]

/-- Freeing the last set slot leaves slot `0` alone. -/
theorem free₁_bvar_zero {M n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    Semiproposition.free₁ (t ∈# (0 : Fin (M + 2)) : Semiproposition ℒₒᵣ (M + 2) n)
      = (t ∈# (0 : Fin (M + 1))) := by
  show SecondOrder.Rew.free.app (t ∈# (0 : Fin (M + 2))) = _
  rw [SecondOrder.Rew.app_bvar]
  simp [SecondOrder.Rew.free]

theorem freeN₁'_bvar_zero {n : ℕ} : ∀ (M : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n),
    freeN₁' M (t ∈# (0 : Fin (M + 1))) = (t ∈# (0 : Fin 1))
  | 0, _ => rfl
  | M + 1, t => by rw [freeN₁'_succ, free₁_bvar_zero, freeN₁'_bvar_zero M t]

/-- **Freeing the last set slot commutes with pushing every slot up by one.**
The one fact the comprehension instantiation turns on. -/
theorem free_bRight_succ {M : ℕ} :
    (SecondOrder.Rew.free (L := ℒₒᵣ) (ξ := ℕ) (N := M + 1)).bRight
        (Fin.succ : Fin (M + 1) → Fin (M + 2))
      = (SecondOrder.Rew.free (L := ℒₒᵣ) (ξ := ℕ) (N := M)).bLeft
        (Fin.succ : Fin M → Fin (M + 1)) := by
  ext X
  · cases X using Fin.lastCases with
    | cast i => simp [-Fin.castSucc_succ, Fin.succ_castSucc]
    | last => simp
  · simp

theorem free₁_bmap_succ {M n : ℕ} (χ : Semiproposition ℒₒᵣ (M + 1) n) :
    Semiproposition.free₁ (χ.bmap (Fin.succ : Fin (M + 1) → Fin (M + 2)))
      = (Semiproposition.free₁ χ).bmap (Fin.succ : Fin M → Fin (M + 1)) := by
  show SecondOrder.Rew.free.app (χ.bmap Fin.succ) = (SecondOrder.Rew.free.app χ).bmap Fin.succ
  rw [SecondOrder.Rew.bmap_app_eq, SecondOrder.Rew.app_bmap_eq_bLeft, free_bRight_succ]

/-- **The comprehended set's slot is never touched.**  Freeing all `M` set
parameters out of `χ.bmap Fin.succ` leaves a `bmap` from the *empty* set of
slots — which is why the `(∃₂)` witness is simply `freeN₁ M χ`. -/
theorem freeN₁'_bmap_succ {n : ℕ} : ∀ (M : ℕ) (χ : Semiproposition ℒₒᵣ M n),
    freeN₁' M (χ.bmap (Fin.succ : Fin M → Fin (M + 1)))
      = (freeN₁ M χ).bmap (Fin.succ : Fin 0 → Fin 1)
  | 0, _ => rfl
  | M + 1, χ => by
      rw [freeN₁'_succ, free₁_bmap_succ, freeN₁'_bmap_succ M (Semiproposition.free₁ χ),
        freeN₁_succ]

/-! ### Arithmeticity survives the freeing -/

theorem arith_free₁ {N n : ℕ} {φ : Semiproposition ℒₒᵣ (N + 1) n} (h : Arith φ) :
    Arith (Semiproposition.free₁ φ) :=
  arith_app φ h SecondOrder.Rew.free
    (fun X => by cases X using Fin.lastCases <;> simp) (fun X => by simp)

theorem arith_freeN₁ : ∀ (M : ℕ) {n : ℕ} {φ : Semiproposition ℒₒᵣ M n},
    Arith φ → Arith (freeN₁ M φ)
  | 0, _, _, h => h
  | M + 1, _, _, h => arith_freeN₁ M (arith_free₁ h)

/-! ### The comprehension leaf -/

theorem subst_bRight_empty (C : Semiproposition ℒₒᵣ 0 1) :
    (SecondOrder.Rew.subst ![C]).bRight (Fin.succ : Fin 0 → Fin 1)
      = (SecondOrder.Rew.id : SecondOrder.Rew ℒₒᵣ ℕ 0 ℕ 0 ℕ) := by
  ext X
  · exact X.elim0
  · simp

theorem subst₂_bmap_succ {n : ℕ} (C : Semiproposition ℒₒᵣ 0 1)
    (D : Semiproposition ℒₒᵣ 0 n) :
    (SecondOrder.Rew.subst ![C]).app (D.bmap (Fin.succ : Fin 0 → Fin 1)) = D := by
  rw [SecondOrder.Rew.bmap_app_eq, subst_bRight_empty, SecondOrder.Rew.app_id]

/-- **Substituting the witness back gives `C ↔ C`.** -/
theorem subst_compBody_leaf (C : Semiproposition ℒₒᵣ 0 1) :
    ((∀¹ (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)) 🡘
        (C.bmap (Fin.succ : Fin 0 → Fin 1)))) : Semiproposition ℒₒᵣ 1 0)/⟦C⟧
      = ∀¹ (C 🡘 C) := by
  show (SecondOrder.Rew.subst ![C]).app _ = _
  rw [SecondOrder.Rew.app_all₀]
  congr 1
  simp only [LogicalConnective.iff, LogicalConnective.DeMorgan.imply,
    LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, SecondOrder.Rew.app_bvar,
    SecondOrder.Rew.subst_bv, Matrix.cons_val_fin_one, subst₂_bmap_succ]
  rw [subst_bvar_self]

section Leaf

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

theorem iff_self_all₁_derivable (C : Semiproposition ℒₒᵣ 0 1) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (OrdinalNotation.ofNat 3)
      [ev₂ (∀¹ (C 🡘 C))] := by
  refine all₁_step (fun _ => OrdinalNotation.ofNat 2)
    (fun _ => OrdinalNotation.ofNat_lt_ofNat (by omega)) (fun m => ?_)
  have e : ev₂ ((C 🡘 C)/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)])
      = (ev₂ (C/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)]))
        🡘 (ev₂ (C/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)])) := by
    simp [LogicalConnective.iff, LogicalConnective.DeMorgan.imply]
  rw [e]
  exact iff_self_derivable _ le_rfl

/-- **A fully freed, fully instantiated comprehension body is derivable at
height `4`.** -/
theorem compBody_leaf_derivable (C : Semiproposition ℒₒᵣ 0 1) (hC : Arith C) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (OrdinalNotation.ofNat 4)
      [ev₂ (∃² (∀¹ (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)) 🡘
        (C.bmap (Fin.succ : Fin 0 → Fin 1)))))] := by
  refine exs₂_step hC (OrdinalNotation.ofNat_lt_ofNat (show 3 < 4 by omega)) ?_
  rw [subst_compBody_leaf]
  exact iff_self_all₁_derivable C

end Leaf

/-! ### The instantiation computation for comprehension -/

theorem freeN₁_compBody {N n : ℕ} (ψ : Semiproposition ℒₒᵣ N (n + 1)) :
    freeN₁ N (compBody ψ)
      = ∃² (∀¹ (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1)) ∈# (0 : Fin 1)) 🡘
          ((freeN₁ N ψ).bmap (Fin.succ : Fin 0 → Fin 1)))) := by
  rw [compBody, freeN₁_exs₂, freeN₁'_all₁, freeN₁'_iff, freeN₁'_bvar_zero, freeN₁'_bmap_succ]

theorem subst_compBody {N n : ℕ} (ψ : Semiproposition ℒₒᵣ N (n + 1)) (w : Fin n → ℕ) :
    FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))
        ▹ (freeN₁ N (compBody ψ))
      = ∃² (∀¹ (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)) 🡘
          (((FirstOrder.Rew.subst
              (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q
            ▹ (freeN₁ N ψ)).bmap (Fin.succ : Fin 0 → Fin 1)))) := by
  rw [freeN₁_compBody]
  simp [LogicalConnective.iff, LogicalConnective.DeMorgan.imply, ← Semiformula.bmap_comm]

/-- **Every instance of arithmetical comprehension is cut-free derivable at a
height below `ε₀`** — at `(4 ⊕ n) ⊕ N`. -/
theorem arithComp₂_derivable_lt_eps₀ {N n : ℕ} (ψ : Semiproposition ℒₒᵣ N (n + 1))
    (hψ : Arith ψ) :
    ∃ β : Gamma0Note, β < epsZero ∧
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ (arithComp₂ ψ)] := by
  have hbody : ∀ w : Fin n → ℕ, OmegaDerivable₂ trueArithLits₂ evInst₂ 0
      (OrdinalNotation.ofNat 4 : Gamma0Note)
      [ev₂ (FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))
        ▹ (freeN₁ N (compBody ψ)))] := by
    intro w
    rw [subst_compBody]
    exact compBody_leaf_derivable _ ((arith_rew _ _).mpr (arith_freeN₁ N hψ))
  have h1 := allN₁_derivable (freeN₁ N (compBody ψ)) hbody
  rw [← freeN₁_allN₁] at h1
  have h2 := allN₂_derivable (allN₁ n (compBody ψ)) h1
  rw [allN₁_eq_allNums, allN₂_eq_allSets] at h2
  refine ⟨_, ?_, h2⟩
  exact nadd_lt_epsZero (nadd_lt_epsZero (ofNat_lt_epsZero 4) (ofNat_lt_epsZero n))
    (ofNat_lt_epsZero N)

/-- The scheme form. -/
theorem arithComp₂_derivable {N n : ℕ} (ψ : Semiproposition ℒₒᵣ N (n + 1)) (hψ : Arith ψ) :
    ∃ β : Gamma0Note, β < epsEps ∧
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ (arithComp₂ ψ)] :=
  let ⟨β, hβ, hd⟩ := arithComp₂_derivable_lt_eps₀ ψ hψ
  ⟨β, lt_trans hβ epsZero_lt_epsEps, hd⟩

/-! ### Every axiom of `ACA` -/

/-- `Axioms₂.aca_logical_axiom_derivable`, with the sharper bound.  Every height
there is `ω + k` for a `k ≤ 5`, so `< ε₀` holds just as `< ε_{ε₀}` does. -/
theorem acaCore_derivable_lt_eps₀ (χ : Proposition ℒₒᵣ) (h : χ ∈ acaCore) :
    ∃ β : Gamma0Note, β < epsZero ∧
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ χ] := by
  rcases h with (h | h) | h | h
  · exact ⟨hgt₂ χ, ofNat_lt_epsZero _, eq_axiom_derivable χ h⟩
  · exact ⟨hgt₂ χ, ofNat_lt_epsZero _, paMinus_axiom_derivable χ h⟩
  · refine ⟨OrdinalNotation.nadd omegaG (OrdinalNotation.ofNat 3),
      nadd_lt_epsZero omegaG_lt_epsZero (ofNat_lt_epsZero 3), ?_⟩
    rw [h]
    exact setInduction_derivable
  · refine ⟨OrdinalNotation.ofNat 5, ofNat_lt_epsZero 5, ?_⟩
    rw [h]
    exact setExt_derivable

/-- **Every axiom of `ACA` is cut-free derivable at a height below `ε₀`.**  This
is the hypothesis `cut_axioms₂_of` consumes, with the bound the second cut
elimination needs. -/
theorem aca_axiom_derivable_lt_eps₀ (σ : Proposition ℒₒᵣ) (h : σ ∈ ACA) :
    ∃ β : Gamma0Note, β < epsZero ∧
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ σ] := by
  rcases h with (h | ⟨N, n, ψ, hψ, -, -, rfl⟩) | ⟨N, n, φ, -, -, rfl⟩
  · exact acaCore_derivable_lt_eps₀ σ h
  · exact arithComp₂_derivable_lt_eps₀ ψ hψ
  · exact indScheme₂_derivable_lt_eps₀ φ

/-- The scheme form. -/
theorem aca_axiom_derivable (σ : Proposition ℒₒᵣ) (h : σ ∈ ACA) :
    ∃ β : Gamma0Note, β < epsEps ∧
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ σ] :=
  let ⟨β, hβ, hd⟩ := aca_axiom_derivable_lt_eps₀ σ h
  ⟨β, lt_trans hβ epsZero_lt_epsEps, hd⟩

end SchemeAxioms₂

end OrdinalAnalysis.ACAOmega
