/- Source: OrdinalAnalysis\ID1\AxiomsPA.lean (one-level `Omega` generalised to the top level
`Omega (n - 1)`; `AxDerivable`/`axDerivable_of_le` taken as hypotheses, `OrdinalAnalysis.IDn.
AxiomsLogic` not yet ported). -/

import OrdinalAnalysis.IDn.NumSubst
import OrdinalAnalysis.IDn.Sound
/-
  The induction axioms of `PA` over `(LXIn n)` in the infinitary calculus of `ID n`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, proof of Theorem 6.5: "the axioms of `PA ⊆ ID₁`,
  including induction for the extended language `L_ID`, are treated as in the proof of
  Theorem 3.7 from the first lecture". Per §2.5 of the design note, the multi-level statement
  has no mathematics beyond `ID1.AxiomsPA`: every height is measured against the *top* `Ω_n`
  (`ThetaWNoteD.Omega (n - 1)`), since the induction scheme ranges over all of `L_ID` (which may
  mention any `I_k`) but is otherwise level-free.

  **The argument** (Theorem 3.7 of the first lecture, for the ω-rule).  For the body `ψ` of
  an induction axiom, with its free variables already replaced by numerals, the chain

      ¬ψ(0), ∃x (ψ(x) ∧ ¬ψ(x + 1)), ψ(m̄)          at height ω · rk ψ ⊕ 2m

  is built by induction on `m`: the base is Lemma 6.1, and the step is clause (W) on the
  existential at the witness `m̄`, with the conjunction `ψ(m̄) ∧ ¬ψ(m̄ + 1)` from the chain
  for `m` and from Lemma 6.1 for `ψ(m+1)`.  The instance `ψ(m̄ + 1)` of the induction step and
  the numeral `ψ((m+1)‾)` of the ω-rule differ in a closed term of the same value; Freund's
  remark on the replacement of closed terms (`IDnDerivable.replace_head`) reconciles them.  The
  ω-rule then gives `∀x ψ(x)` at height `ω · rk ψ ⊕ ω`, two disjunction steps the axiom, and
  the universal closure is peeled by the ω-rule once for every free variable.

  Contents.

    `embT_numeral`, `sucX`, `sucI`, `embT_sucX`, `val_subst_sucI`
    `succIndI`, `numSubst_embK_succInd`   the embedded axiom under a numeral assignment
    `chain`, `succIndI_derivable`
    `omegaMul_nadd`                       `ω · (α ⊕ β) = ω · α ⊕ ω · β`
    `induction_axiom`                     **every induction axiom**

  Not yet ported (`OrdinalAnalysis.IDn.AxiomsLogic`, in flight): the axiom-derivability
  predicate `AxDerivable`/`axDerivable_of_le` are taken here as hypotheses with the `ID1`
  statement lifted to the top level. `OmegaTwo_pa` itself and its
  elementary membership/comparison facts do not depend on that file's development, so they are
  proved locally instead of hypothesised.
-/

set_option autoImplicit false

namespace OrdinalAnalysis
variable {n : ℕ} (k : Fin n)

namespace ThetaWNoteD

/-- **`ω · (α ⊕ β) = ω · α ⊕ ω · β`**: both exponent lists are the non-increasing arrangement
of the same entries `1 + α_i`, `1 + β_j`. -/
theorem omegaMul_nadd (a b : ThetaWNoteD) :
    omegaMul (ThetaWNoteD.nadd a b) = ThetaWNoteD.nadd (omegaMul a) (omegaMul b) :=
  ext_entries (by
    have h1 := sorted_entries (omegaMul (ThetaWNoteD.nadd a b))
    have h2 := sorted_entries (ThetaWNoteD.nadd (omegaMul a) (omegaMul b))
    rw [entries_omegaMul, entries_nadd] at h1
    rw [entries_nadd, entries_omegaMul, entries_omegaMul] at h2
    rw [entries_omegaMul, entries_nadd, entries_nadd, entries_omegaMul, entries_omegaMul]
    refine ThetaWTerm.eq_of_perm_of_sortedDesc h1 h2 ?_
    refine ((ThetaWTerm.mergeL_perm _ _).map _).trans ?_
    rw [List.map_append]
    exact (ThetaWTerm.mergeL_perm _ _).symm)

/-- **Finite ordinal and natural increments agree**: `α + m = α ⊕ m`. Ported from
`ID1.AxiomsID.add_ofNat_eq_nadd` (not a general library lemma there either): needed here since
`IDn.Rank.rk_le_add_ofNat` states its bound with ordinal `+`, not `nadd`. -/
theorem add_ofNat_eq_nadd (a : ThetaWNoteD) :
    ∀ m : ℕ, a + ThetaWNoteD.ofNat m = ThetaWNoteD.nadd a (ThetaWNoteD.ofNat m)
  | 0 => by rw [ThetaWNoteD.ofNat_zero, ThetaWNoteD.add_zero, ThetaWNoteD.nadd_zero]
  | m + 1 => by
    have e1 : a + ThetaWNoteD.ofNat (m + 1) = (a + ThetaWNoteD.ofNat m) + ThetaWNoteD.one := by
      rw [ThetaWNoteD.add_assoc, ThetaWNoteD.add_one_eq_succ, ← ThetaWNoteD.ofNat_succ]
    rw [e1, ThetaWNoteD.add_one_eq_succ, ThetaWNoteD.add_ofNat_eq_nadd a m, ThetaWNoteD.ofNat_succ]
    show ThetaWNoteD.nadd (ThetaWNoteD.nadd a (ThetaWNoteD.ofNat m)) ThetaWNoteD.one =
      ThetaWNoteD.nadd a (ThetaWNoteD.nadd (ThetaWNoteD.ofNat m) ThetaWNoteD.one)
    rw [ThetaWNoteD.nadd_assoc]

/-- `Ω_i ≤ Ω_j` whenever `i ≤ j`. -/
theorem Omega_le_Omega_of_le_pa {i j : ℕ} (h : i ≤ j) : ThetaWNoteD.Omega i ≤ ThetaWNoteD.Omega j := by
  rcases h.lt_or_eq with hlt | rfl
  · exact le_of_lt (ThetaWNoteD.Omega_lt_Omega_iff.mpr hlt)
  · exact le_refl _


/-- `a ⊕ 1 = succ a` (`succ a` is defined as `nadd a one`, `ofNat 1 = one`). Ported from
`ID1.AxiomsLogic.nadd_ofNat_one_pa` (not yet a general library lemma; `IDn.AxiomsLogic` has this
same content but does not compile at the time of this port). -/
theorem nadd_ofNat_one_pa (a : ThetaWNoteD) : ThetaWNoteD.nadd a (ThetaWNoteD.ofNat 1) = ThetaWNoteD.succ a := by
  rw [ThetaWNoteD.ofNat_one]; rfl

theorem lt_nadd_ofNat_succ_pa (a : ThetaWNoteD) (p : ℕ) : a < ThetaWNoteD.nadd a (ThetaWNoteD.ofNat (p + 1)) :=
  lt_of_lt_of_le (ThetaWNoteD.lt_succ a) (by
    rw [← ThetaWNoteD.nadd_ofNat_one_pa]
    exact ThetaWNoteD.nadd_le_nadd_right a (ThetaWNoteD.ofNat_le_ofNat (by omega)))

theorem ofNat_lt_nadd_ofNat_succ_pa (a : ThetaWNoteD) (p : ℕ) :
    ThetaWNoteD.ofNat p < ThetaWNoteD.nadd a (ThetaWNoteD.ofNat (p + 1)) :=
  lt_of_lt_of_le (ThetaWNoteD.ofNat_lt_ofNat (Nat.lt_succ_self p)) (ThetaWNoteD.le_nadd_right _ _)

theorem nadd_ofNat_lt_nadd_ofNat_pa (a : ThetaWNoteD) {j p : ℕ} (h : j < p) :
    ThetaWNoteD.nadd a (ThetaWNoteD.ofNat j) < ThetaWNoteD.nadd a (ThetaWNoteD.ofNat p) :=
  ThetaWNoteD.nadd_lt_nadd_right a (ThetaWNoteD.ofNat_lt_ofNat h)

end ThetaWNoteD

namespace IDn

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting
open LO.FirstOrder.Arithmetic

/-! ### The `Set ThetaWNoteD` view of a single formula's parameters -/

section ParamsAt

variable {ξ : Type*} {m : ℕ}

/-- **`k(φ)` with the level tag erased** — `IDn.CalculusAux.paramsVal`'s singleton counterpart
(not yet in that file): the operator `H : Set ThetaWNoteD → Set ThetaWNoteD` is level-free, so
a single formula's control condition is phrased against this set, not against
`params φ : Set (Stage n)` directly. -/
def paramsAt (φ : Semiformula (LIinfN n) ξ m) : Set ThetaWNoteD := Stage.val '' params φ

theorem paramsAt_and (φ ψ : Semiformula (LIinfN n) ξ m) :
    paramsAt (φ ⋏ ψ) = paramsAt φ ∪ paramsAt ψ := by
  simp [paramsAt, params_and, Set.image_union]

theorem paramsAt_or (φ ψ : Semiformula (LIinfN n) ξ m) :
    paramsAt (φ ⋎ ψ) = paramsAt φ ∪ paramsAt ψ := by
  simp [paramsAt, params_or, Set.image_union]

theorem paramsAt_neg (φ : Semiformula (LIinfN n) ξ m) : paramsAt (∼φ) = paramsAt φ := by
  simp [paramsAt, params_neg]

theorem paramsAt_all (φ : Semiformula (LIinfN n) ξ (m + 1)) : paramsAt (∀¹ φ) = paramsAt φ := by
  simp [paramsAt, params_all]

theorem paramsAt_exs (φ : Semiformula (LIinfN n) ξ (m + 1)) : paramsAt (∃¹ φ) = paramsAt φ := by
  simp [paramsAt, params_exs]

theorem paramsAt_subst (φ : Semiformula (LIinfN n) ξ 1) {l : ℕ} (t : Semiterm (LIinfN n) ξ l) :
    paramsAt (φ/[t]) = paramsAt φ := by
  simp [paramsAt]

/-- **`paramsAt` does not see terms**: invariant under every rewriting, not just substitution
into the one free variable (`paramsAt_subst`'s general form, matching `Language.params_rew`). -/
theorem paramsAt_rew {ξ' : Type*} {l l' : ℕ} (ω : Rew (LIinfN n) ξ l ξ' l')
    (φ : Semiformula (LIinfN n) ξ l) : paramsAt (ω ▹ φ) = paramsAt φ := by
  simp [paramsAt, params_rew]

theorem paramsAt_subst_sub {ψ : Semiformula (LIinfN n) ξ 1} {S : Set ThetaWNoteD}
    (hp : paramsAt ψ ⊆ S) {l : ℕ} (t : Semiterm (LIinfN n) ξ l) : paramsAt (ψ/[t]) ⊆ S := by
  rw [paramsAt_subst]; exact hp

/-- Every embedded atom `I_j` sits at its own top `Ω_{j+1} ≤ Ω_n`, so an embedded formula's
parameters lie in any nice `H ∅` unconditionally. The `IDn` generalisation of `ID1.AxiomsPA`'s
use of `params_embK` (there bounded by the single `{Ω}`; here by every level's own top). -/
theorem paramsAt_embK {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    {ξ' : Type*} {l : ℕ} (φ : Semiformula (LXIn n) ξ' l) : paramsAt (embK φ) ⊆ H ∅ := by
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨j, rfl⟩ := params_embK φ hs
  exact hH.Omega_mem j.val

end ParamsAt

variable {A : Fin n → Semisentence (LXIn n) 1}

/-! ### Not yet ported (`OrdinalAnalysis.IDn.AxiomsLogic`, in flight)

`taut`, `OmegaTwo_pa`/`AxDerivable`/`axDerivable_of_le` are `ID1.AxiomsLogic` content; that file
exists in `IDn` but does not yet reach these declarations (checked at draft time: it has
`taut_and` but not the final `taut`). For a dependency "not on disk
yet", they are taken here as hypotheses with the `ID1` statement lifted to the top level
`Ω_n = Omega (n - 1)`. `omegaT_pa := ω^1` and `Ω_n · 2` themselves
do not depend on that file's development, so they are defined locally. -/

abbrev omegaT_pa : ThetaWNoteD := ThetaWNoteD.omegaPow ThetaWNoteD.one

abbrev OmegaTwo_pa : ThetaWNoteD :=
  ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) (ThetaWNoteD.Omega (n - 1))

/-- `ofNat c < ω = omegaT_pa`, generic Foundation-level arithmetic (`ID1.Rank.ofNat_lt_omega`,
not yet a general `ThetaWNoteD` library lemma). -/
theorem ofNat_lt_omegaT (c : ℕ) : ThetaWNoteD.ofNat c < omegaT_pa := by
  rw [omegaT_pa, ThetaWNoteD.lt_omegaPow_iff, ThetaWNoteD.entries_ofNat]
  intro e he
  rw [List.eq_of_mem_replicate he]
  exact ThetaWNoteD.zero_lt_one

/- `rew_numeral` and `xFreeI_neg` used to be reproved locally here (importing `IDn.Evaluate`
redeclared `XFreeL`, already defined by `NumSubst`, into the same namespace). `NumSubst.lean` has
since been updated (by its owner, mid-session) to delete its temporary duplicate `XFree` section
and `import OrdinalAnalysis.IDn.Evaluate` directly, exactly as that file's own docstring asked —
so both are now available transitively through `NumSubst`, and a local copy here would collide
with them (`has already been declared`). -/

/-- Substituting a closed term for the one free variable of a formula closed outside it keeps
it closed (`IDn.AxiomsLogic.freeVariables_subst_of_closed_pa`, reproved locally for the same
reason as `rew_numeral`). -/
theorem freeVariables_subst_of_closed_pa (φ : Semiformula (LIinfN n) ℕ 1) (hφ : φ.freeVariables = ∅)
    {t : SyntacticTerm (LIinfN n)} (ht : t.freeVariables = ∅) : (φ/[t]).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![t]) (φ := φ) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ ((Rew.subst ![t]) #i : SyntacticTerm (LIinfN n)).freeVariables := hi
    cases i using Fin.cases with
    | zero => simp only [Rew.subst_bvar, Matrix.cons_val_zero, ht] at hi'
              exact Finset.notMem_empty x hi'
    | succ i => exact i.elim0
  · have hz' : z ∈ φ.freeVariables := hz
    rw [hφ] at hz'
    exact Finset.notMem_empty z hz'

variable (AxDerivable : (Fin n → Semisentence (LXIn n) 1) → Sentence (LXIn n) → Prop)

/-- The `taut` hypothesis (`IDn.AxiomsLogic.taut`, ID1's Lemma 6.1): not threaded via
`variable`/`include` — combined with `axDerivable_of_le`/`val_numI` (see below) that hit an
unrelated async-elaboration `AddConstAsyncResult.commitConst` failure on this Lean toolchain
(reproduced with `omit`/`include` both ways). A plain explicit argument on each theorem that
needs it avoids it entirely (mirrors `IDn.AxiomsLogic`'s own `ValNumIHyp` workaround for the
same bug). -/
abbrev TautHyp (A : Fin n → Semisentence (LXIn n) 1) : Prop :=
  ∀ {H : Set ThetaWNoteD → Set ThetaWNoteD}, ThetaWNoteD.NiceS H →
    ∀ (ψ : Proposition (LIinfN n)), ψ.freeVariables = ∅ →
    IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (paramsAt ψ))
      (ThetaWNoteD.omegaMul (rk ψ)) [ψ, ∼ψ]

/-- The `axDerivable_of_le` hypothesis (`IDn.AxiomsLogic`/`IDn.Embed`'s `axDerivable_of_le`),
explicit for the same reason as `TautHyp`. -/
abbrev AxDerivableOfLeHyp (A : Fin n → Semisentence (LXIn n) 1)
    (AxDerivable : (Fin n → Semisentence (LXIn n) 1) → Sentence (LXIn n) → Prop) : Prop :=
  ∀ {σ : Sentence (LXIn n)} (m : ℕ) (h : ThetaWNoteD),
      h ≤ ThetaWNoteD.nadd (OmegaTwo_pa (n := n)) (ThetaWNoteD.ofNat m) →
      (∀ H : Set ThetaWNoteD → Set ThetaWNoteD, ThetaWNoteD.NiceS H →
        IDnDerivable A ThetaWNoteD.zero H h [(Rewriting.emb (embK σ) : Proposition (LIinfN n))]) →
      AxDerivable A σ

/- Also not yet usable: `IDn.Evaluate.val_numI`/`val_numeral_stdInfN` exist on disk, but that
file's own `XFreeL` collides with `NumSubst`'s (both define it independently — a cross-file
bug between the two "in flight" ports, out of this file's scope),
so importing it breaks the build. `val_numI` is a pure numeral-evaluation fact, taken as a
hypothesis here with the `ID1` statement unchanged (level-independent), explicit for the same
reason as `TautHyp`/`AxDerivableOfLeHyp` (matches `IDn.AxiomsLogic.ValNumIHyp`). -/
abbrev ValNumIHyp (n : ℕ) : Prop := ∀ (m : ℕ) (e : Fin 0 → ℕ) (ε : ℕ → ℕ),
    Semiterm.val (s := (@stdInfN n)) e ε (@numI n m) = m

/-- The `allClosure_derivable` hypothesis (`IDn.AxiomsLogic`'s `allClosure_derivable`, not yet
on disk — its own `Contents` docstring lists it but the file does not yet reach it; `ID1`'s
statement, lifted to `(LIinfN n)`/`IDnDerivable`), explicit for the same reason as the other
hypotheses above (and because it is only ever needed once, in `induction_axiom`). -/
abbrev AllClosureDerivableHyp (A : Fin n → Semisentence (LXIn n) 1) : Prop :=
  ∀ {H : Set ThetaWNoteD → Set ThetaWNoteD}, ThetaWNoteD.IsOperator H → ∀ {l : ℕ}
    (σ : Semiformula (LIinfN n) ℕ l) {β : ThetaWNoteD},
    (∀ j : ℕ, ThetaWNoteD.nadd β (ThetaWNoteD.ofNat j) ∈ H ∅) → paramsAt σ ⊆ H ∅ →
    (∀ w : Fin l → ℕ, IDnDerivable A ThetaWNoteD.zero H β [σ ⇜ fun i => numI (w i)]) →
    IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.nadd β (ThetaWNoteD.ofNat l)) [∀¹* σ]

/-- `Sim`/`sim_subst_closed`/`IDnDerivable.replace_head` (`IDn.Evaluate`, Freund's remark on
term replacement by a closed term of the same value, used in `chain`): genuinely exist and are
green on disk in `IDn/Evaluate.lean`, but that file cannot be imported here either — it
duplicates `NumSubst`'s temporary `XFreeL`/`IsXRelN`/… section verbatim (`NumSubst.lean`'s own
docstring: "whoever writes `IDn/Evaluate.lean` should delete this section and import it
instead", not yet done — out of this file's scope). Taken as hypotheses with `Evaluate`'s own
statements, unchanged beyond `n`/`A`/`H`. -/
abbrev SimRel (n : ℕ) : Type := {m : ℕ} → Semiformula (LIinfN n) ℕ m → Semiformula (LIinfN n) ℕ m → Prop

abbrev SimSubstClosedHyp (n : ℕ) (Sim : SimRel n) : Prop :=
  ∀ {m : ℕ} {φ : Semiformula (LIinfN n) ℕ 1}, φ.freeVariables = ∅ → XFreeI φ →
    ∀ {s t : Semiterm (LIinfN n) ℕ m}, s.freeVariables = ∅ → t.freeVariables = ∅ →
    (∀ (e : Fin m → ℕ) (ε : ℕ → ℕ),
      Semiterm.val (s := (@stdInfN n)) e ε s = Semiterm.val (s := (@stdInfN n)) e ε t) →
    Sim (Rew.subst ![s] ▹ φ) (Rew.subst ![t] ▹ φ)

abbrev ReplaceHeadHyp (n : ℕ) (A : Fin n → Semisentence (LXIn n) 1) (Sim : SimRel n) : Prop :=
  (∀ j, XFreeL (A j)) →
    ∀ {H : Set ThetaWNoteD → Set ThetaWNoteD}, ThetaWNoteD.IsOperator H →
    ∀ {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)} {φ φ' : Proposition (LIinfN n)},
    IDnDerivable A ThetaWNoteD.zero H α (φ :: Γ) → Sim φ φ' →
    IDnDerivable A ThetaWNoteD.zero H α (φ' :: Γ)

/-! ### Terms under the embedding -/

section Terms

variable {ξ : Type*} {m : ℕ}

private lemma embT_numeral_zero :
    embT k ((0 : ℕ) : Semiterm (LXIn n) ξ m) = ((0 : ℕ) : Semiterm (LIinfN n) ξ m) := by
  rw [embT, stageHom_top]
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, embedHom, stageFuncN]
  rfl

private lemma embT_numeral_one :
    embT k ((1 : ℕ) : Semiterm (LXIn n) ξ m) = ((1 : ℕ) : Semiterm (LIinfN n) ξ m) := by
  rw [embT, stageHom_top]
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, embedHom, stageFuncN]
  rfl

theorem embT_add (v : Fin 2 → Semiterm (LXIn n) ξ m) :
    embT k (Semiterm.Operator.Add.add.operator v) =
      Semiterm.Operator.Add.add.operator (embT k ∘ v) := by
  rw [embT, stageHom_top]
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func]
  refine congrArg (Semiterm.func (Language.Add.add : (LIinfN n).Func 2)) ?_
  funext i
  show Semiterm.lMap embedHom (v i) = embT k (v i)
  rw [embT, stageHom_top]

private lemma numeralX_succ_succ (L : Language) [L.Zero] [L.One] [L.Add] (c : ℕ) :
    ((c + 1 + 1 : ℕ) : Semiterm L ξ m) =
      Semiterm.Operator.Add.add.operator
        ![((c + 1 : ℕ) : Semiterm L ξ m), ((1 : ℕ) : Semiterm L ξ m)] := by
  have h : c + 1 ≠ 0 := Nat.succ_ne_zero c
  simp only [Semiterm.numeral, Semiterm.Operator.const,
    Semiterm.Operator.numeral_succ h, Semiterm.Operator.operator_comp]
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- The embedding fixes the numerals. -/
theorem embT_numeral (c : ℕ) :
    embT k ((c : ℕ) : Semiterm (LXIn n) ξ m) = ((c : ℕ) : Semiterm (LIinfN n) ξ m) := by
  induction c with
  | zero => exact embT_numeral_zero k
  | succ c ih =>
    cases c with
    | zero => exact embT_numeral_one k
    | succ c =>
      rw [numeralX_succ_succ (LXIn n) c, numeralX_succ_succ (LIinfN n) c, embT_add]
      congr 1
      funext i
      match i with
      | ⟨0, _⟩ => exact ih
      | ⟨1, _⟩ => exact embT_numeral_one k

end Terms

/-- The successor term `#0 + 1` of `(LXIn n)`. -/
def sucX : Semiterm (LXIn n) ℕ 1 := ‘(#0 + 1)’

/-- The successor term `#0 + 1` of `(LIinfN n)`. -/
def sucI : Semiterm (LIinfN n) ℕ 1 := ‘(#0 + 1)’

theorem embT_sucX : embT k sucX = sucI := by
  rw [sucX, sucI]
  show embT k (Semiterm.Operator.Add.add.operator ![#0, ((1 : ℕ) : Semiterm (LXIn n) ℕ 1)]) = _
  rw [embT_add]
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => exact embT_numeral k 1

/-- `+` in operator form is `+` in function form. -/
theorem add_operator_eq_func {m : ℕ} (a b : Semiterm (LIinfN n) ℕ m) :
    Semiterm.Operator.Add.add.operator ![a, b]
      = Semiterm.func (Language.Add.add : (LIinfN n).Func 2) ![a, b] := by
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func]
  exact congrArg (Semiterm.func (Language.Add.add : (LIinfN n).Func 2))
    (by funext i; match i with
        | ⟨0, _⟩ => simp
        | ⟨1, _⟩ => simp)

theorem subst_sucI (t : SyntacticTerm (LIinfN n)) :
    Rew.subst ![t] sucI =
      Semiterm.func (Language.Add.add : (LIinfN n).Func 2) ![t, ((1 : ℕ) : SyntacticTerm (LIinfN n))] := by
  rw [← add_operator_eq_func]
  simp [sucI]

/-- The successor term with a closed term substituted has the successor value. -/
theorem val_subst_sucI
    (t : SyntacticTerm (LIinfN n))
    (e : Fin 0 → ℕ) (ε : ℕ → ℕ) :
    Semiterm.val (s := stdInfN) e ε (Rew.subst ![t] sucI) =
      Semiterm.val (s := stdInfN) e ε t + 1 := by
  rw [subst_sucI, Semiterm.val_func]
  change Semiterm.val (s := stdInfN) e ε t +
    Semiterm.val (s := stdInfN) e ε (numI 1) = _
  rw [val_numI]

theorem freeVariables_subst_sucI {t : SyntacticTerm (LIinfN n)} (ht : t.freeVariables = ∅) :
    (Rew.subst ![t] sucI).freeVariables = ∅ := by
  rw [subst_sucI, Semiterm.freeVariables_func]
  ext x
  simp only [Finset.notMem_empty, iff_false, Finset.mem_biUnion, Finset.mem_univ, true_and,
    not_exists]
  intro i hx
  match i with
  | ⟨0, h⟩ =>
    have h0 : (![t, ((1 : ℕ) : SyntacticTerm (LIinfN n))] : Fin 2 → SyntacticTerm (LIinfN n)) ⟨0, h⟩ = t :=
      rfl
    rw [h0, ht] at hx
    exact Finset.notMem_empty x hx
  | ⟨1, h⟩ =>
    have h1 : (![t, ((1 : ℕ) : SyntacticTerm (LIinfN n))] : Fin 2 → SyntacticTerm (LIinfN n)) ⟨1, h⟩ =
        ((1 : ℕ) : SyntacticTerm (LIinfN n)) := rfl
    rw [h1, numeral_freeVariables] at hx
    exact Finset.notMem_empty x hx

theorem OmegaTwo_mem_pa {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    (X : Set ThetaWNoteD) (m : ℕ) :
    ThetaWNoteD.nadd (OmegaTwo_pa (n := n)) (ThetaWNoteD.ofNat m) ∈ H X :=
  hH.nadd_mem (hH.nadd_mem (hH.Omega_mem (n - 1)) (hH.Omega_mem (n - 1))) (hH.ofNat_mem m)

theorem Omega_le_OmegaTwo_nadd_pa (m : ℕ) :
    ThetaWNoteD.Omega (n - 1) ≤ ThetaWNoteD.nadd (OmegaTwo_pa (n := n)) (ThetaWNoteD.ofNat m) :=
  le_trans (ThetaWNoteD.le_nadd_left _ _) (ThetaWNoteD.le_nadd_left _ _)

/-! ### The embedded induction axiom -/

section Induction

variable {H : Set ThetaWNoteD → Set ThetaWNoteD}

/-- The induction axiom for the body `ψ`, in `(LIinfN n)`. -/
def succIndI (ψ : Semiformula (LIinfN n) ℕ 1) : Proposition (LIinfN n) :=
  (ψ/[numI 0]) 🡒 (∀¹ (ψ/[(#0 : Semiterm (LIinfN n) ℕ 1)] 🡒 ψ/[sucI])) 🡒
    ∀¹ (ψ/[(#0 : Semiterm (LIinfN n) ℕ 1)])

/-- The body of the existential that the negated induction step is. -/
def stepBody (ψ : Semiformula (LIinfN n) ℕ 1) : Semiformula (LIinfN n) ℕ 1 :=
  ψ/[(#0 : Semiterm (LIinfN n) ℕ 1)] ⋏ ∼(ψ/[sucI])

theorem succInd_eq (φ : Semiformula (LXIn n) ℕ 1) :
    succInd φ = (φ/[((0 : ℕ) : SyntacticTerm (LXIn n))]) 🡒
      (∀¹ (φ/[(#0 : Semiterm (LXIn n) ℕ 1)] 🡒 φ/[sucX])) 🡒 ∀¹ (φ/[(#0 : Semiterm (LXIn n) ℕ 1)]) := rfl

theorem numSubst₁_subst (g : ℕ → ℕ) (s : Semiterm (LIinfN n) ℕ 1) (φ : Semiformula (LIinfN n) ℕ 1) :
    numSubst₁ g ▹ (φ/[s]) = (numSubst₁ g ▹ φ)/[numSubst₁ g s] := by
  simpa [← comp_app] using smul_ext' (φ := φ) <| by ext x <;> simp [Rew.comp_app, numSubst₁]

theorem numSubst₁_sucI (g : ℕ → ℕ) : numSubst₁ g (sucI : Semiterm (LIinfN n) ℕ 1) = sucI := by
  simp [sucI, numSubst₁]

include k in
/-- **A numeral assignment passes through the embedded induction axiom.** -/
theorem numSubst_embK_succInd (g : ℕ → ℕ) (φ : Semiformula (LXIn n) ℕ 1) :
    numSubst g ▹ embK (succInd φ) = succIndI (numSubst₁ g ▹ embK φ) := by
  rw [succInd_eq, succIndI]
  simp only [Semiformula.imp_eq, embK_or, embK_neg, embK_all, (embK_subst₁ k), embT_numeral,
    embT_sucX, Semiterm.lMap_bvar, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, numSubst_all, numSubst_subst, rew_numeral]
  rw [numSubst₁_subst, numSubst₁_subst, numSubst₁_sucI, numSubst₁_bvar]

/-- Substituting into a substitution instance. -/
theorem subst_subst₁ (ψ : Semiformula (LIinfN n) ℕ 1) (s : Semiterm (LIinfN n) ℕ 1)
    (t : SyntacticTerm (LIinfN n)) : (ψ/[s])/[t] = ψ/[Rew.subst ![t] s] := by
  simpa [← comp_app] using smul_ext' (φ := ψ) <| by ext x <;> simp [Rew.comp_app]

theorem subst_bvar_subst (ψ : Semiformula (LIinfN n) ℕ 1) (t : SyntacticTerm (LIinfN n)) :
    (ψ/[(#0 : Semiterm (LIinfN n) ℕ 1)])/[t] = ψ/[t] := by
  rw [subst_subst₁]; simp

theorem stepBody_inst (ψ : Semiformula (LIinfN n) ℕ 1) (m : ℕ) :
    (stepBody ψ)/[numI m] = ψ/[numI m] ⋏ ∼(ψ/[Rew.subst ![numI m] sucI]) := by
  show (Rew.subst ![numI m]) ▹ (ψ/[(#0 : Semiterm (LIinfN n) ℕ 1)] ⋏ ∼(ψ/[sucI])) = _
  rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg]
  congr 1
  · exact subst_bvar_subst ψ _
  · exact congrArg _ (subst_subst₁ ψ _ _)

theorem neg_step (ψ : Semiformula (LIinfN n) ℕ 1) :
    ∼(∀¹ (ψ/[(#0 : Semiterm (LIinfN n) ℕ 1)] 🡒 ψ/[sucI])) = ∃¹ stepBody ψ := by
  simp [stepBody, Semiformula.imp_eq]

/-- **The chain** (first lecture, proof of Theorem 3.7): from `¬ψ(0)`, the negated induction
step and `ψ(m̄)` in the sequent, a cut-free derivation of height `ω · rk ψ ⊕ 2m`. -/
theorem chain (taut : TautHyp A)
    (Sim : SimRel n) (sim_subst_closed : SimSubstClosedHyp n Sim)
    (replace_head : ReplaceHeadHyp n A Sim)
    (hA : ∀ j, XFreeL (A j)) (hH : ThetaWNoteD.NiceS H) (ψ : Semiformula (LIinfN n) ℕ 1)
    (hf : ψ.freeVariables = ∅) (hX : XFreeI ψ) (hp : paramsAt ψ ⊆ H ∅) :
    ∀ (m : ℕ) (Γ : Sequent (LIinfN n)), ∼(ψ/[numI 0]) ∈ Γ → (∃¹ stepBody ψ) ∈ Γ →
      ψ/[numI m] ∈ Γ → paramsVal Γ ⊆ H ∅ →
      IDnDerivable A ThetaWNoteD.zero H
        (ThetaWNoteD.nadd (ThetaWNoteD.omegaMul (rk ψ)) (ThetaWNoteD.ofNat (2 * m))) Γ := by
  have hK : ∀ t : SyntacticTerm (LIinfN n), ThetaWNoteD.adjoin H (paramsAt (ψ/[t])) = H := fun t =>
    ThetaWNoteD.adjoin_eq_self hH.1 (paramsAt_subst_sub hp t)
  have hrk : ∀ t : SyntacticTerm (LIinfN n), rk (ψ/[t]) = rk ψ := fun t => rk_subst ψ t
  have hmem : ∀ c : ℕ, ThetaWNoteD.nadd (ThetaWNoteD.omegaMul (rk ψ)) (ThetaWNoteD.ofNat c) ∈ H ∅ :=
    fun c => hH.nadd_mem (hH.omegaMul_mem (hH.rk_mem (fun s hs => hp ⟨s, hs, rfl⟩))) (hH.ofNat_mem c)
  have taut' : ∀ t : SyntacticTerm (LIinfN n), t.freeVariables = ∅ →
      IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.omegaMul (rk ψ)) [ψ/[t], ∼(ψ/[t])] := by
    intro t ht
    have d := taut hH (ψ/[t]) (freeVariables_subst_of_closed_pa ψ hf ht)
    rwa [hK t, hrk t] at d
  intro m
  induction m with
  | zero =>
    intro Γ h0 _ hn hP
    rw [Nat.mul_zero, ThetaWNoteD.ofNat_zero, ThetaWNoteD.nadd_zero]
    refine (taut' (numI 0) (numI_freeVariables 0)).weaken_seq hH.1 ?_ hP
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hn
    · exact h0
  | succ m ih =>
    intro Γ h0 hS hn hP
    set inst : Proposition (LIinfN n) := (stepBody ψ)/[numI m] with hinst
    have hinst' : inst = ψ/[numI m] ⋏ ∼(ψ/[Rew.subst ![numI m] sucI]) := stepBody_inst ψ m
    have pinst : paramsAt inst ⊆ H ∅ := by rw [hinst, paramsAt_subst, stepBody, paramsAt_and,
      paramsAt_neg, paramsAt_subst, paramsAt_subst, Set.union_self]; exact hp
    have hP1 : paramsVal (inst :: Γ) ⊆ H ∅ := by
      rw [paramsVal_cons]; exact Set.union_subset pinst hP
    have hP2 : ∀ χ : Proposition (LIinfN n), paramsAt χ ⊆ H ∅ → paramsVal (χ :: inst :: Γ) ⊆ H ∅ := by
      intro χ hχ; rw [paramsVal_cons]; exact Set.union_subset hχ hP1
    -- the left conjunct, from the chain for `m`
    have d1 : IDnDerivable A ThetaWNoteD.zero H
        (ThetaWNoteD.nadd (ThetaWNoteD.omegaMul (rk ψ)) (ThetaWNoteD.ofNat (2 * m)))
        (ψ/[numI m] :: inst :: Γ) :=
      ih _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h0))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hS)) List.mem_cons_self
        (hP2 _ (paramsAt_subst_sub hp _))
    -- the right conjunct, from Lemma 6.1 at the numeral `(m+1)‾` and term replacement
    have hsuc : (Rew.subst ![numI m] sucI).freeVariables = ∅ :=
      freeVariables_subst_sucI (n := n) (t := numI m) (numI_freeVariables (n := n) m)
    have d2' : IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.omegaMul (rk ψ))
        (∼(ψ/[numI (m + 1)]) :: inst :: Γ) :=
      (taut' (numI (m + 1)) (numI_freeVariables _)).weaken_seq hH.1 (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hn)
        · exact List.mem_cons_self) (hP2 _ (by rw [paramsAt_neg]; exact paramsAt_subst_sub hp _))
    have hsim : Sim (∼(ψ/[numI (m + 1)])) (∼(ψ/[Rew.subst ![numI m] sucI])) := by
      have := sim_subst_closed (m := 0) (φ := ∼ψ) (by rw [Semiformula.freeVariables_not]; exact hf)
        ((xFreeI_neg ψ).mpr hX) (numI_freeVariables (m + 1)) hsuc (fun e ε => by
          rw [val_subst_sucI, val_numI, val_numI])
      simpa using this
    have d2 : IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.omegaMul (rk ψ))
        (∼(ψ/[Rew.subst ![numI m] sucI]) :: inst :: Γ) :=
      replace_head hA hH.1 d2' hsim
    have hlt1 : ThetaWNoteD.nadd (ThetaWNoteD.omegaMul (rk ψ)) (ThetaWNoteD.ofNat (2 * m)) <
        ThetaWNoteD.nadd (ThetaWNoteD.omegaMul (rk ψ)) (ThetaWNoteD.ofNat (2 * m + 1)) :=
      ThetaWNoteD.nadd_ofNat_lt_nadd_ofNat_pa _ (by omega)
    have hlt2 : ThetaWNoteD.omegaMul (rk ψ) <
        ThetaWNoteD.nadd (ThetaWNoteD.omegaMul (rk ψ)) (ThetaWNoteD.ofNat (2 * m + 1)) :=
      ThetaWNoteD.lt_nadd_ofNat_succ_pa _ _
    have d3 : IDnDerivable A ThetaWNoteD.zero H
        (ThetaWNoteD.nadd (ThetaWNoteD.omegaMul (rk ψ)) (ThetaWNoteD.ofNat (2 * m + 1)))
        (inst :: Γ) :=
      .and (hmem _) hP1 (by rw [← hinst']; exact List.mem_cons_self) hlt1 hlt2 d1 d2
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
    exact .exs m (hmem _) hP hS (lt_of_lt_of_le (ThetaWNoteD.ofNat_lt_ofNat (by omega))
      (ThetaWNoteD.le_nadd_right _ _)) (ThetaWNoteD.nadd_ofNat_lt_nadd_ofNat_pa _ (by omega)) d3

/-- **The induction axiom for a body without free variables**, cut-free, at height
`ω · rk ψ ⊕ ω ⊕ 4`. -/
theorem succIndI_derivable (taut : TautHyp A)
    (Sim : SimRel n) (sim_subst_closed : SimSubstClosedHyp n Sim)
    (replace_head : ReplaceHeadHyp n A Sim)
    (hA : ∀ j, XFreeL (A j)) (hH : ThetaWNoteD.NiceS H) (ψ : Semiformula (LIinfN n) ℕ 1)
    (hf : ψ.freeVariables = ∅) (hX : XFreeI ψ) (hp : paramsAt ψ ⊆ H ∅) :
    IDnDerivable A ThetaWNoteD.zero H
      (ThetaWNoteD.nadd (ThetaWNoteD.nadd (ThetaWNoteD.omegaMul (rk ψ)) omegaT_pa) (ThetaWNoteD.ofNat 4))
      [succIndI ψ] := by
  set hω : ThetaWNoteD := ThetaWNoteD.nadd (ThetaWNoteD.omegaMul (rk ψ)) omegaT_pa with hhω
  have hmem : ∀ c : ℕ, ThetaWNoteD.nadd hω (ThetaWNoteD.ofNat c) ∈ H ∅ := fun c =>
    hH.nadd_mem (hH.nadd_mem (hH.omegaMul_mem (hH.rk_mem (fun s hs => hp ⟨s, hs, rfl⟩))) (hH.omegaPow_mem hH.one_mem))
      (hH.ofNat_mem c)
  have hlt : ∀ j c : ℕ, j < c → ThetaWNoteD.nadd hω (ThetaWNoteD.ofNat j) <
      ThetaWNoteD.nadd hω (ThetaWNoteD.ofNat c) := fun j c h => ThetaWNoteD.nadd_ofNat_lt_nadd_ofNat_pa _ h
  have h0 : ThetaWNoteD.nadd hω (ThetaWNoteD.ofNat 0) = hω := by
    rw [ThetaWNoteD.ofNat_zero, ThetaWNoteD.nadd_zero]
  have hone : ∀ c, ThetaWNoteD.one < ThetaWNoteD.nadd hω (ThetaWNoteD.ofNat c) := fun c =>
    lt_of_lt_of_le (by rw [← ThetaWNoteD.ofNat_one]; exact ofNat_lt_omegaT 1)
      (le_trans (ThetaWNoteD.le_nadd_right _ _) (ThetaWNoteD.le_nadd_left _ _))
  set Z : Proposition (LIinfN n) := ∼(ψ/[numI 0]) with hZ
  set S : Proposition (LIinfN n) := ∃¹ stepBody ψ with hS
  set U : Proposition (LIinfN n) := ∀¹ (ψ/[(#0 : Semiterm (LIinfN n) ℕ 1)]) with hU
  have eM : succIndI ψ = Z ⋎ (S ⋎ U) := by
    rw [succIndI, Semiformula.imp_eq, Semiformula.imp_eq, neg_step]
  have pZ : paramsAt Z ⊆ H ∅ := by rw [hZ, paramsAt_neg]; exact paramsAt_subst_sub hp _
  have pS : paramsAt S ⊆ H ∅ := by
    rw [hS, paramsAt_exs, stepBody, paramsAt_and, paramsAt_neg, paramsAt_subst, paramsAt_subst,
      Set.union_self]; exact hp
  have pU : paramsAt U ⊆ H ∅ := by rw [hU, paramsAt_all]; exact paramsAt_subst_sub hp _
  have pM : paramsAt (succIndI ψ) ⊆ H ∅ := by
    rw [eM, paramsAt_or, paramsAt_or]; exact Set.union_subset pZ (Set.union_subset pS pU)
  have pl : ∀ Γ : Sequent (LIinfN n), (∀ χ ∈ Γ, paramsAt χ ⊆ H ∅) → paramsVal Γ ⊆ H ∅ := by
    intro Γ h
    induction Γ with
    | nil => simp [paramsVal]
    | cons φ Γ ihΓ =>
      rw [paramsVal_cons]
      exact Set.union_subset (h φ List.mem_cons_self) (ihΓ fun χ hχ => h χ (List.mem_cons_of_mem _ hχ))
  -- the ω-rule
  have dω : IDnDerivable A ThetaWNoteD.zero H hω [U, Z, S, S ⋎ U, succIndI ψ] := by
    refine .all (fun m => ThetaWNoteD.nadd (ThetaWNoteD.omegaMul (rk ψ))
      (ThetaWNoteD.ofNat (2 * m))) (by rw [← h0]; exact hmem 0) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl | rfl | rfl
        · exact pU
        · exact pZ
        · exact pS
        · rw [paramsAt_or]; exact Set.union_subset pS pU
        · exact pM)) List.mem_cons_self
      (fun m => ThetaWNoteD.nadd_lt_nadd_right _ (ofNat_lt_omegaT _)) (fun m => ?_)
    rw [subst_bvar_subst]
    refine chain taut Sim sim_subst_closed replace_head hA hH ψ hf hX hp m _ ?_ ?_
      List.mem_cons_self ?_
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self))
    · refine pl _ ?_
      intro χ hχ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
      rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl
      · exact paramsAt_subst_sub hp _
      · exact pU
      · exact pZ
      · exact pS
      · rw [paramsAt_or]; exact Set.union_subset pS pU
      · exact pM
  have pSU : paramsAt (S ⋎ U) ⊆ H ∅ := by rw [paramsAt_or]; exact Set.union_subset pS pU
  have d1 : IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.nadd hω (ThetaWNoteD.ofNat 1))
      [Z, S, S ⋎ U, succIndI ψ] :=
    .orR (hmem 1) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl | rfl
        · exact pZ
        · exact pS
        · exact pSU
        · exact pM))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (hone 1)
      (ThetaWNoteD.lt_nadd_ofNat_succ_pa hω 0) dω
  have d2 : IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.nadd hω (ThetaWNoteD.ofNat 2))
      [Z, S ⋎ U, succIndI ψ] :=
    .orL (hmem 2) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl
        · exact pZ
        · exact pSU
        · exact pM))
      (List.mem_cons_of_mem _ List.mem_cons_self) (hlt 1 2 (by omega))
      (d1.weaken_seq hH.1 (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        tauto) (pl _ (by
          intro χ hχ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
          rcases hχ with rfl | rfl | rfl | rfl
          · exact pS
          · exact pZ
          · exact pSU
          · exact pM)))
  have d3 : IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.nadd hω (ThetaWNoteD.ofNat 3))
      [Z, succIndI ψ] :=
    .orR (hmem 3) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl
        · exact pZ
        · exact pM))
      (by rw [eM]; exact List.mem_cons_of_mem _ List.mem_cons_self) (hone 3)
      (hlt 2 3 (by omega))
      (d2.weaken_seq hH.1 (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        tauto) (pl _ (by
          intro χ hχ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
          rcases hχ with rfl | rfl | rfl
          · exact pSU
          · exact pZ
          · exact pM)))
  exact .orL (hmem 4) (pl _ (by
      intro χ hχ
      rw [List.mem_singleton.mp hχ]; exact pM))
    (by rw [eM]; exact List.mem_cons_self) (hlt 3 4 (by omega)) d3

end Induction

/-! ### Height bounds -/

section Bounds

/-- **`rk φ ⪯ Ω_n ⊕ ω · c`**, `c` the complexity of `φ` — every parameter of `φ` is some
level's own top `Ω_{j+1} ≤ Ω_n`, so `IDn.Rank.rk_le_add_ofNat` applies unconditionally. The
`IDn` analogue of `ID1.Rank.rk_le_Omega_nadd`. -/
theorem rk_le_Omega_nadd {ξ : Type*} {m : ℕ} (φ : Semiformula (LIinfN n) ξ m) :
    rk φ ≤ ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) (ThetaWNoteD.ofNat φ.complexity) := by
  rw [← ThetaWNoteD.add_ofNat_eq_nadd]
  exact rk_le_add_ofNat (fun s _ => by
    obtain ⟨j, b⟩ := s
    exact le_trans (atomRkStage_mk_le_Omega j b) (ThetaWNoteD.Omega_le_Omega_of_le_pa (by omega)))

/-- `ω · rk φ ⪯ Ω_n ⊕ ω · c`, `c` the complexity of `φ`. -/
theorem omegaMul_rk_le {ξ : Type*} {m : ℕ} (φ : Semiformula (LIinfN n) ξ m) :
    ThetaWNoteD.omegaMul (rk φ) ≤
      ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1))
        (ThetaWNoteD.omegaMul (ThetaWNoteD.ofNat φ.complexity)) := by
  rw [← ThetaWNoteD.omegaMul_Omega (n - 1), ← ThetaWNoteD.omegaMul_nadd]
  exact ThetaWNoteD.omegaMul_le_omegaMul (rk_le_Omega_nadd φ)

theorem omegaMul_ofNat_lt_Omega (c : ℕ) :
    ThetaWNoteD.omegaMul (ThetaWNoteD.ofNat c) < ThetaWNoteD.Omega (n - 1) :=
  ThetaWNoteD.omegaMul_lt_prin trivial (ThetaWNoteD.ofNat_lt_prin (p := ThetaWNoteD.Omega (n - 1)) trivial c)

/-- `Ω_n ⊕ y ⪯ Ω_n · 2` for `y ≺ Ω_n`. -/
theorem nadd_Omega_le_OmegaTwo {y : ThetaWNoteD} (hy : y < ThetaWNoteD.Omega (n - 1)) (m : ℕ) :
    ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) y ≤
      ThetaWNoteD.nadd (OmegaTwo_pa (n := n)) (ThetaWNoteD.ofNat m) :=
  le_trans (ThetaWNoteD.nadd_le_nadd_right _ (le_of_lt hy)) (ThetaWNoteD.le_nadd_left _ _)

end Bounds

/-! ### The induction axioms -/

section InductionAxiom

/-- Numerals of `(LXIn n)`. -/
abbrev numX (m : ℕ) : SyntacticTerm (LXIn n) := Semiterm.numeral m

include k in
theorem embK_rewrite_numX (g : ℕ → ℕ) (ψ : Proposition (LXIn n)) :
    embK (Rew.rewrite (fun x => numX (g x)) ▹ ψ) = numSubst g ▹ embK ψ := by
  rw [embK, killX_rew, embed, Semiformula.lMap_rewrite, embK, embed, numSubst]
  have e : (Semiterm.lMap embedHom ∘ fun x => (numX (g x) : SyntacticTerm (LXIn n))) =
      fun x => (numI (g x) : SyntacticTerm (LIinfN n)) := by
    funext x
    show Semiterm.lMap embedHom (numX (g x)) = numI (g x)
    rw [← stageHom_top k]
    exact embT_numeral k (g x)
  rw [e]

theorem emb_embK_univCl (ψ : Proposition (LXIn n)) :
    (Rewriting.emb (embK (Semiformula.univCl ψ)) : Proposition (LIinfN n)) =
      ∀¹* (embK (Rew.fixitr 0 ψ.fvSup ▹ ψ)) := by
  rw [← embK_emb, Semiformula.coe_univCl_eq_univCl', Semiformula.univCl', embK_allClosure]

include k in
theorem embK_fixitr_inst (ψ : Proposition (LXIn n)) (w : Fin (0 + ψ.fvSup) → ℕ) :
    (embK (Rew.fixitr 0 ψ.fvSup ▹ ψ) ⇜ fun i => numI (w i)) =
      numSubst (fun y => if hy : y < 0 + ψ.fvSup then w ⟨y, hy⟩ else 0) ▹ embK ψ := by
  have e1 : (fun i : Fin (0 + ψ.fvSup) => (numI (w i) : SyntacticTerm (LIinfN n))) =
      embT k ∘ (fun i : Fin (0 + ψ.fvSup) => (numX (w i) : SyntacticTerm (LXIn n))) := by
    funext i
    exact (embT_numeral k (w i)).symm
  rw [e1, ← embK_subst k, ← embK_rewrite_numX k]
  congr 1
  have e2 : (fun i : Fin (0 + ψ.fvSup) => (numX (w i) : SyntacticTerm (LXIn n))) =
      fun i : Fin (0 + ψ.fvSup) =>
        (fun y : ℕ => (numX (if hy : y < 0 + ψ.fvSup then w ⟨y, hy⟩ else 0) : SyntacticTerm (LXIn n)))
          (i : ℕ) := by
    funext i
    simp only [dif_pos i.isLt, Fin.eta]
  rw [e2]
  exact Semiformula.subst_comp_fixitr_eq_map ψ
    (fun y => numX (if hy : y < 0 + ψ.fvSup then w ⟨y, hy⟩ else 0))

include k in
/-- **Every induction axiom of `paLXIN (Fin n)`** (Freund, proof of Theorem 6.5, after Theorem
3.7 of the first lecture): cut-free, at a height below `Ω_n · 2`. -/
theorem induction_axiom (taut : TautHyp A)
    (Sim : SimRel n) (sim_subst_closed : SimSubstClosedHyp n Sim)
    (replace_head : ReplaceHeadHyp n A Sim)
    (axDerivable_of_le : AxDerivableOfLeHyp A AxDerivable)
    (allClosure_derivable : AllClosureDerivableHyp A) (hA : ∀ j, XFreeL (A j)) {σ : Sentence (LXIn n)}
    (h : σ ∈ InductionScheme (LXIn n) Set.univ) : AxDerivable A σ := by
  obtain ⟨φ, -, rfl⟩ := h
  set ψ0 : Proposition (LXIn n) := succInd φ with hψ0
  set β : ThetaWNoteD := ThetaWNoteD.nadd (ThetaWNoteD.nadd (ThetaWNoteD.omegaMul (rk (embK φ))) omegaT_pa)
    (ThetaWNoteD.ofNat 4) with hβ
  refine axDerivable_of_le (0 + ψ0.fvSup)
    (ThetaWNoteD.nadd β (ThetaWNoteD.ofNat (0 + ψ0.fvSup))) ?_ (fun H hH => ?_)
  · have h1 : β ≤ ThetaWNoteD.nadd (ThetaWNoteD.nadd (ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1))
        (ThetaWNoteD.omegaMul (ThetaWNoteD.ofNat (embK φ).complexity))) omegaT_pa) (ThetaWNoteD.ofNat 4) :=
      ThetaWNoteD.nadd_le_nadd_left' _ (ThetaWNoteD.nadd_le_nadd_left' _ (omegaMul_rk_le _))
    refine le_trans (ThetaWNoteD.nadd_le_nadd_left' _ h1) ?_
    rw [ThetaWNoteD.nadd_assoc, ThetaWNoteD.nadd_assoc, ThetaWNoteD.nadd_assoc]
    refine nadd_Omega_le_OmegaTwo ?_ _
    exact ThetaWNoteD.nadd_lt_Omega (omegaMul_ofNat_lt_Omega _)
      (ThetaWNoteD.nadd_lt_Omega (ThetaWNoteD.omegaPow_lt_Omega
        (ThetaWNoteD.one_lt_prin (p := ThetaWNoteD.Omega (n - 1)) trivial))
        (ThetaWNoteD.nadd_lt_Omega (ThetaWNoteD.ofNat_lt_prin (p := ThetaWNoteD.Omega (n - 1)) trivial _)
          (ThetaWNoteD.ofNat_lt_prin (p := ThetaWNoteD.Omega (n - 1)) trivial _)))
  · have hpK : ∀ {m : ℕ} (χ : Semiformula (LXIn n) ℕ m), paramsAt (embK χ) ⊆ H ∅ :=
      fun χ => paramsAt_embK hH χ
    rw [emb_embK_univCl]
    refine allClosure_derivable hH.1 _ (fun j => hH.nadd_mem (hH.nadd_mem
      (hH.nadd_mem (hH.omegaMul_mem (hH.rk_mem (fun s hs => hpK φ ⟨s, hs, rfl⟩))) (hH.omegaPow_mem hH.one_mem))
      (hH.ofNat_mem 4)) (hH.ofNat_mem j)) (hpK (Rew.fixitr 0 ψ0.fvSup ▹ ψ0)) (fun w => ?_)
    rw [embK_fixitr_inst k, numSubst_embK_succInd k]
    set g : ℕ → ℕ := fun y => if hy : y < 0 + ψ0.fvSup then w ⟨y, hy⟩ else 0 with hg
    have d := succIndI_derivable taut Sim sim_subst_closed replace_head hA hH
      (numSubst₁ g ▹ embK φ) (freeVariables_numSubst₁ g _)
      ((xFreeI_rew (numSubst₁ g) _).mpr (xFreeI_embK φ)) (by rw [paramsAt_rew]; exact hpK φ)
    rwa [rk_rew] at d

end InductionAxiom

end IDn

end OrdinalAnalysis
