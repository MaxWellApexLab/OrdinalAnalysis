/- Source: OrdinalAnalysis\IDn\AxiomsPA.lean (ID_n -> ID_omega: `LXJ`, `Jlev ⊤` embedding, level-free `OmegaW`). -/

import OrdinalAnalysis.IDw.NumSubst
import OrdinalAnalysis.IDw.Sound
/- Source: OrdinalAnalysis\ID1\AxiomsPA.lean (one-level `Omega` generalised to the top level
`Omega (n - 1)`; `AxDerivable`/`axDerivable_of_le` taken as hypotheses, `OrdinalAnalysis.IDw.
AxiomsLogic` not yet ported). -/

/-
  The induction axioms of `PA` over `(LXJ)` in the infinitary calculus of `ID n`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, proof of Theorem 6.5: "the axioms of `PA ⊆ ID₁`,
  including induction for the extended language `L_ID`, are treated as in the proof of
  Theorem 3.7 from the first lecture". Per §2.5 of the design note, the multi-level statement
  has no mathematics beyond `ID1.AxiomsPA`: every height is measured against the *top* `Ω_n`
  (`ThetaVNoteD.OmegaW`), since the induction scheme ranges over all of `L_ID` (which may
  mention any `I_k`) but is otherwise level-free.

  **The argument** (Theorem 3.7 of the first lecture, for the ω-rule).  For the body `ψ` of
  an induction axiom, with its free variables already replaced by numerals, the chain

      ¬ψ(0), ∃x (ψ(x) ∧ ¬ψ(x + 1)), ψ(m̄)          at height ω · rk ψ ⊕ 2m

  is built by induction on `m`: the base is Lemma 6.1, and the step is clause (W) on the
  existential at the witness `m̄`, with the conjunction `ψ(m̄) ∧ ¬ψ(m̄ + 1)` from the chain
  for `m` and from Lemma 6.1 for `ψ(m+1)`.  The instance `ψ(m̄ + 1)` of the induction step and
  the numeral `ψ((m+1)‾)` of the ω-rule differ in a closed term of the same value; Freund's
  remark on the replacement of closed terms (`IDwDerivable.replace_head`) reconciles them.  The
  ω-rule then gives `∀x ψ(x)` at height `ω · rk ψ ⊕ ω`, two disjunction steps the axiom, and
  the universal closure is peeled by the ω-rule once for every free variable.

  Contents.

    `embT_numeral`, `sucX`, `sucI`, `embT_sucX`, `val_subst_sucI`
    `succIndI`, `numSubst_embK_succInd`   the embedded axiom under a numeral assignment
    `chain`, `succIndI_derivable`
    `omegaMul_nadd`                       `ω · (α ⊕ β) = ω · α ⊕ ω · β`
    `induction_axiom`                     **every induction axiom**

  Not yet ported (`OrdinalAnalysis.IDw.AxiomsLogic`, in flight): the axiom-derivability
  predicate `AxDerivable`/`axDerivable_of_le` are taken here as hypotheses with the `ID1`
  statement lifted to the top level. `OmegaTwo_pa` itself and its
  elementary membership/comparison facts do not depend on that file's development, so they are
  proved locally instead of hypothesised.
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaVNoteD

/-- **`ω · (α ⊕ β) = ω · α ⊕ ω · β`**: both exponent lists are the non-increasing arrangement
of the same entries `1 + α_i`, `1 + β_j`. -/
theorem omegaMul_nadd (a b : ThetaVNoteD) :
    omegaMul (ThetaVNoteD.nadd a b) = ThetaVNoteD.nadd (omegaMul a) (omegaMul b) :=
  ext_entries (by
    have h1 := sorted_entries (omegaMul (ThetaVNoteD.nadd a b))
    have h2 := sorted_entries (ThetaVNoteD.nadd (omegaMul a) (omegaMul b))
    rw [entries_omegaMul, entries_nadd] at h1
    rw [entries_nadd, entries_omegaMul, entries_omegaMul] at h2
    rw [entries_omegaMul, entries_nadd, entries_nadd, entries_omegaMul, entries_omegaMul]
    refine ThetaVTerm.eq_of_perm_of_sortedDesc h1 h2 ?_
    refine ((ThetaVTerm.mergeL_perm _ _).map _).trans ?_
    rw [List.map_append]
    exact (ThetaVTerm.mergeL_perm _ _).symm)

/-- **Finite ordinal and natural increments agree**: `α + m = α ⊕ m`. Ported from
`ID1.AxiomsID.add_ofNat_eq_nadd` (not a general library lemma there either): needed here since
`IDw.Rank.rk_le_add_ofNat` states its bound with ordinal `+`, not `nadd`. -/
theorem add_ofNat_eq_nadd (a : ThetaVNoteD) :
    ∀ m : ℕ, a + ThetaVNoteD.ofNat m = ThetaVNoteD.nadd a (ThetaVNoteD.ofNat m)
  | 0 => by rw [ThetaVNoteD.ofNat_zero, ThetaVNoteD.add_zero, ThetaVNoteD.nadd_zero]
  | m + 1 => by
    have e1 : a + ThetaVNoteD.ofNat (m + 1) = (a + ThetaVNoteD.ofNat m) + ThetaVNoteD.one := by
      rw [ThetaVNoteD.add_assoc, ThetaVNoteD.add_one_eq_succ, ← ThetaVNoteD.ofNat_succ]
    rw [e1, ThetaVNoteD.add_one_eq_succ, ThetaVNoteD.add_ofNat_eq_nadd a m, ThetaVNoteD.ofNat_succ]
    show ThetaVNoteD.nadd (ThetaVNoteD.nadd a (ThetaVNoteD.ofNat m)) ThetaVNoteD.one =
      ThetaVNoteD.nadd a (ThetaVNoteD.nadd (ThetaVNoteD.ofNat m) ThetaVNoteD.one)
    rw [ThetaVNoteD.nadd_assoc]

/-- `Ω_i ≤ Ω_j` whenever `i ≤ j`. -/
theorem Omega_le_Omega_of_le_pa {i j : ℕ} (h : i ≤ j) : ThetaVNoteD.Omega i ≤ ThetaVNoteD.Omega j := by
  rcases h.lt_or_eq with hlt | rfl
  · exact le_of_lt (ThetaVNoteD.Omega_lt_Omega_iff.mpr hlt)
  · exact le_refl _


/-- `a ⊕ 1 = succ a` (`succ a` is defined as `nadd a one`, `ofNat 1 = one`). Ported from
`ID1.AxiomsLogic.nadd_ofNat_one_pa` (not yet a general library lemma; `IDw.AxiomsLogic` has this
same content but does not compile at the time of this port). -/
theorem nadd_ofNat_one_pa (a : ThetaVNoteD) : ThetaVNoteD.nadd a (ThetaVNoteD.ofNat 1) = ThetaVNoteD.succ a := by
  rw [ThetaVNoteD.ofNat_one]; rfl

theorem lt_nadd_ofNat_succ_pa (a : ThetaVNoteD) (p : ℕ) : a < ThetaVNoteD.nadd a (ThetaVNoteD.ofNat (p + 1)) :=
  lt_of_lt_of_le (ThetaVNoteD.lt_succ a) (by
    rw [← ThetaVNoteD.nadd_ofNat_one_pa]
    exact ThetaVNoteD.nadd_le_nadd_right a (ThetaVNoteD.ofNat_le_ofNat (by omega)))

theorem ofNat_lt_nadd_ofNat_succ_pa (a : ThetaVNoteD) (p : ℕ) :
    ThetaVNoteD.ofNat p < ThetaVNoteD.nadd a (ThetaVNoteD.ofNat (p + 1)) :=
  lt_of_lt_of_le (ThetaVNoteD.ofNat_lt_ofNat (Nat.lt_succ_self p)) (ThetaVNoteD.le_nadd_right _ _)

theorem nadd_ofNat_lt_nadd_ofNat_pa (a : ThetaVNoteD) {j p : ℕ} (h : j < p) :
    ThetaVNoteD.nadd a (ThetaVNoteD.ofNat j) < ThetaVNoteD.nadd a (ThetaVNoteD.ofNat p) :=
  ThetaVNoteD.nadd_lt_nadd_right a (ThetaVNoteD.ofNat_lt_ofNat h)

end ThetaVNoteD

namespace IDw

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting
open LO.FirstOrder.Arithmetic

/-! ### The `Set ThetaVNoteD` view of a single formula's parameters -/

section ParamsAt

variable {ξ : Type*} {m : ℕ}

/-- **`k(φ)` with the level tag erased** — `IDw.CalculusAux.paramsVal`'s singleton counterpart
(not yet in that file): the operator `H : Set ThetaVNoteD → Set ThetaVNoteD` is level-free, so
a single formula's control condition is phrased against this set, not against
`params φ : Set (Stage)` directly. -/
def paramsAt (φ : Semiformula (LIinfW) ξ m) : Set ThetaVNoteD := Stage.val '' params φ

theorem paramsAt_and (φ ψ : Semiformula (LIinfW) ξ m) :
    paramsAt (φ ⋏ ψ) = paramsAt φ ∪ paramsAt ψ := by
  simp [paramsAt, params_and, Set.image_union]

theorem paramsAt_or (φ ψ : Semiformula (LIinfW) ξ m) :
    paramsAt (φ ⋎ ψ) = paramsAt φ ∪ paramsAt ψ := by
  simp [paramsAt, params_or, Set.image_union]

theorem paramsAt_neg (φ : Semiformula (LIinfW) ξ m) : paramsAt (∼φ) = paramsAt φ := by
  simp [paramsAt, params_neg]

theorem paramsAt_all (φ : Semiformula (LIinfW) ξ (m + 1)) : paramsAt (∀¹ φ) = paramsAt φ := by
  simp [paramsAt, params_all]

theorem paramsAt_exs (φ : Semiformula (LIinfW) ξ (m + 1)) : paramsAt (∃¹ φ) = paramsAt φ := by
  simp [paramsAt, params_exs]

theorem paramsAt_subst (φ : Semiformula (LIinfW) ξ 1) {l : ℕ} (t : Semiterm (LIinfW) ξ l) :
    paramsAt (φ/[t]) = paramsAt φ := by
  simp [paramsAt]

/-- **`paramsAt` does not see terms**: invariant under every rewriting, not just substitution
into the one free variable (`paramsAt_subst`'s general form, matching `Language.params_rew`). -/
theorem paramsAt_rew {ξ' : Type*} {l l' : ℕ} (ω : Rew (LIinfW) ξ l ξ' l')
    (φ : Semiformula (LIinfW) ξ l) : paramsAt (ω ▹ φ) = paramsAt φ := by
  simp [paramsAt, params_rew]

theorem paramsAt_subst_sub {ψ : Semiformula (LIinfW) ξ 1} {S : Set ThetaVNoteD}
    (hp : paramsAt ψ ⊆ S) {l : ℕ} (t : Semiterm (LIinfW) ξ l) : paramsAt (ψ/[t]) ⊆ S := by
  rw [paramsAt_subst]; exact hp

/-- An embedded formula has no stage parameters at all (`params_embK : params (embK φ) = ∅`:
the embedding produces only `X`/`Jlev ⊤` atoms), so its parameters lie in any `H ∅`
vacuously (the `hH` argument is kept for the interface). -/
theorem paramsAt_embK {H : Set ThetaVNoteD → Set ThetaVNoteD} (_hH : ThetaVNoteD.NiceS H)
    {ξ' : Type*} {l : ℕ} (φ : Semiformula (LXJ) ξ' l) : paramsAt (embK φ) ⊆ H ∅ := by
  rintro _ ⟨s, hs, rfl⟩
  rw [params_embK φ] at hs
  exact hs.elim

end ParamsAt

variable {A : Semisentence LForm 2}

/-! ### Not yet ported (`OrdinalAnalysis.IDw.AxiomsLogic`, in flight)

`taut`, `OmegaTwo_pa`/`AxDerivable`/`axDerivable_of_le` are `ID1.AxiomsLogic` content; that file
exists in `IDw` but does not yet reach these declarations (checked at draft time: it has
`taut_and` but not the final `taut`). For a dependency "not on disk
yet", they are taken here as hypotheses with the `ID1` statement lifted to the top level
`Ω_n = Omega (n - 1)`. `omegaT_pa := ω^1` and `Ω_n · 2` themselves
do not depend on that file's development, so they are defined locally. -/

abbrev omegaT_pa : ThetaVNoteD := ThetaVNoteD.omegaPow ThetaVNoteD.one

abbrev OmegaTwo_pa : ThetaVNoteD :=
  ThetaVNoteD.nadd ThetaVNoteD.OmegaW ThetaVNoteD.OmegaW

/-- `ofNat c < ω = omegaT_pa`, generic Foundation-level arithmetic (`ID1.Rank.ofNat_lt_omega`,
not yet a general `ThetaVNoteD` library lemma). -/
theorem ofNat_lt_omegaT (c : ℕ) : ThetaVNoteD.ofNat c < omegaT_pa := by
  rw [omegaT_pa, ThetaVNoteD.lt_omegaPow_iff, ThetaVNoteD.entries_ofNat]
  intro e he
  rw [List.eq_of_mem_replicate he]
  exact ThetaVNoteD.zero_lt_one

/- `rew_numeral` and `xFreeI_neg` used to be reproved locally here (importing `IDw.Evaluate`
redeclared `XFreeL`, already defined by `NumSubst`, into the same namespace). `NumSubst.lean` has
since been updated (by its owner, mid-session) to delete its temporary duplicate `XFree` section
and `import OrdinalAnalysis.IDw.Evaluate` directly, exactly as that file's own docstring asked —
so both are now available transitively through `NumSubst`, and a local copy here would collide
with them (`has already been declared`). -/

/-- Substituting a closed term for the one free variable of a formula closed outside it keeps
it closed (`IDw.AxiomsLogic.freeVariables_subst_of_closed_pa`, reproved locally for the same
reason as `rew_numeral`). -/
theorem freeVariables_subst_of_closed_pa (φ : Semiformula (LIinfW) ℕ 1) (hφ : φ.freeVariables = ∅)
    {t : SyntacticTerm (LIinfW)} (ht : t.freeVariables = ∅) : (φ/[t]).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![t]) (φ := φ) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ ((Rew.subst ![t]) #i : SyntacticTerm (LIinfW)).freeVariables := hi
    cases i using Fin.cases with
    | zero => simp only [Rew.subst_bvar, Matrix.cons_val_zero, ht] at hi'
              exact Finset.notMem_empty x hi'
    | succ i => exact i.elim0
  · have hz' : z ∈ φ.freeVariables := hz
    rw [hφ] at hz'
    exact Finset.notMem_empty z hz'

/-! ### `rk φ ∈ H X` from the parameters

`IDw.CalculusAux` does not port `NiceS.rk_mem` (its naive form is false for an arbitrary set
`S`, see the header of that section); for a *nice operator* it is true, because every `Jlev` atom
rank (`Ω_j + 1`, `Ω_ω`) lies in `H X` unconditionally. Proved here, for this file's use. -/

theorem atomRk_mem_pa {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H)
    {X : Set ThetaVNoteD} {k : ℕ} (r : LIinfW.Rel k) (h : ∀ s ∈ relParams r, s.val ∈ H X) :
    atomRk r ∈ H X := by
  rcases r with r | r
  · exact hH.zero_mem
  · cases r with
    | X => exact hH.zero_mem
    | stage s => exact hH.atomRkStage_mem (h s rfl)
    | jlev ℓ =>
      induction ℓ using WithTop.recTopCoe with
      | top => exact hH.OmegaW_mem
      | coe j => exact hH.succ_mem (hH.omegaBelow_mem X j)

theorem rk_mem_pa {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H)
    {X : Set ThetaVNoteD} {ξ : Type*} {m : ℕ} (φ : Semiformula (LIinfW) ξ m)
    (h : ∀ s ∈ params φ, s.val ∈ H X) : rk φ ∈ H X := by
  induction φ using Semiformula.rec' with
  | hverum => rw [rk_verum]; exact hH.zero_mem
  | hfalsum => rw [rk_falsum]; exact hH.zero_mem
  | hrel r v => rw [rk_rel]; exact atomRk_mem_pa hH r h
  | hnrel r v => rw [rk_nrel]; exact atomRk_mem_pa hH r h
  | hand φ ψ ihφ ihψ =>
    rw [rk_and]
    refine hH.succ_mem ?_
    rcases max_choice (rk φ) (rk ψ) with e | e <;> rw [e]
    · exact ihφ fun s hs => h s (Or.inl hs)
    · exact ihψ fun s hs => h s (Or.inr hs)
  | hor φ ψ ihφ ihψ =>
    rw [rk_or]
    refine hH.succ_mem ?_
    rcases max_choice (rk φ) (rk ψ) with e | e <;> rw [e]
    · exact ihφ fun s hs => h s (Or.inl hs)
    · exact ihψ fun s hs => h s (Or.inr hs)
  | hall φ ih => rw [rk_all]; exact hH.succ_mem (ih h)
  | hexs φ ih => rw [rk_exs]; exact hH.succ_mem (ih h)

variable (AxDerivable : (Semisentence LForm 2) → Sentence (LXJ) → Prop)

/-- The `taut` hypothesis (`IDw.AxiomsLogic.taut`, ID1's Lemma 6.1): not threaded via
`variable`/`include` — combined with `axDerivable_of_le`/`val_numI` (see below) that hit an
unrelated async-elaboration `AddConstAsyncResult.commitConst` failure on this Lean toolchain
(reproduced with `omit`/`include` both ways). A plain explicit argument on each theorem that
needs it avoids it entirely (mirrors `IDw.AxiomsLogic`'s own `ValNumIHyp` workaround for the
same bug). -/
abbrev TautHyp (A : Semisentence LForm 2) : Prop :=
  ∀ {H : Set ThetaVNoteD → Set ThetaVNoteD}, ThetaVNoteD.NiceS H →
    ∀ (ψ : Proposition (LIinfW)), ψ.freeVariables = ∅ →
    IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (paramsAt ψ))
      (ThetaVNoteD.omegaMul (rk ψ)) [ψ, ∼ψ]

/-- The `axDerivable_of_le` hypothesis (`IDw.AxiomsLogic`/`IDw.Embed`'s `axDerivable_of_le`),
explicit for the same reason as `TautHyp`. -/
abbrev AxDerivableOfLeHyp (A : Semisentence LForm 2)
    (AxDerivable : (Semisentence LForm 2) → Sentence (LXJ) → Prop) : Prop :=
  ∀ {σ : Sentence (LXJ)} (m : ℕ) (h : ThetaVNoteD),
      h ≤ ThetaVNoteD.nadd OmegaTwo_pa (ThetaVNoteD.ofNat m) →
      (∀ H : Set ThetaVNoteD → Set ThetaVNoteD, ThetaVNoteD.NiceS H →
        IDwDerivable A ThetaVNoteD.zero H h [(Rewriting.emb (embK σ) : Proposition (LIinfW))]) →
      AxDerivable A σ

/- Also not yet usable: `IDw.Evaluate.val_numI`/`val_numeral_stdInfN` exist on disk, but that
file's own `XFreeL` collides with `NumSubst`'s (both define it independently — a cross-file
bug between the two "in flight" ports, out of this file's scope),
so importing it breaks the build. `val_numI` is a pure numeral-evaluation fact, taken as a
hypothesis here with the `ID1` statement unchanged (level-independent), explicit for the same
reason as `TautHyp`/`AxDerivableOfLeHyp` (matches `IDw.AxiomsLogic.ValNumIHyp`). -/
abbrev ValNumIHyp : Prop := ∀ (m : ℕ) (e : Fin 0 → ℕ) (ε : ℕ → ℕ),
    Semiterm.val (s := stdW) e ε (numI m) = m

/-- The `allClosure_derivable` hypothesis (`IDw.AxiomsLogic`'s `allClosure_derivable`, not yet
on disk — its own `Contents` docstring lists it but the file does not yet reach it; `ID1`'s
statement, lifted to `(LIinfW)`/`IDwDerivable`), explicit for the same reason as the other
hypotheses above (and because it is only ever needed once, in `induction_axiom`). -/
abbrev AllClosureDerivableHyp (A : Semisentence LForm 2) : Prop :=
  ∀ {H : Set ThetaVNoteD → Set ThetaVNoteD}, ThetaVNoteD.IsOperator H → ∀ {l : ℕ}
    (σ : Semiformula (LIinfW) ℕ l) {β : ThetaVNoteD},
    (∀ j : ℕ, ThetaVNoteD.nadd β (ThetaVNoteD.ofNat j) ∈ H ∅) → paramsAt σ ⊆ H ∅ →
    (∀ w : Fin l → ℕ, IDwDerivable A ThetaVNoteD.zero H β [σ ⇜ fun i => numI (w i)]) →
    IDwDerivable A ThetaVNoteD.zero H (ThetaVNoteD.nadd β (ThetaVNoteD.ofNat l)) [∀¹* σ]

/-- `Sim`/`sim_subst_closed`/`IDwDerivable.replace_head` (`IDw.Evaluate`, Freund's remark on
term replacement by a closed term of the same value, used in `chain`): genuinely exist and are
green on disk in `IDw/Evaluate.lean`, but that file cannot be imported here either — it
duplicates `NumSubst`'s temporary `XFreeL`/`IsXRelN`/… section verbatim (`NumSubst.lean`'s own
docstring: "whoever writes `IDw/Evaluate.lean` should delete this section and import it
instead", not yet done — out of this file's scope). Taken as hypotheses with `Evaluate`'s own
statements, unchanged beyond `n`/`A`/`H`. -/
abbrev SimRel : Type := {m : ℕ} → Semiformula (LIinfW) ℕ m → Semiformula (LIinfW) ℕ m → Prop

abbrev SimSubstClosedHyp (Sim : SimRel) : Prop :=
  ∀ {m : ℕ} {φ : Semiformula (LIinfW) ℕ 1}, φ.freeVariables = ∅ → XFreeI φ →
    ∀ {s t : Semiterm (LIinfW) ℕ m}, s.freeVariables = ∅ → t.freeVariables = ∅ →
    (∀ (e : Fin m → ℕ) (ε : ℕ → ℕ),
      Semiterm.val (s := stdW) e ε s = Semiterm.val (s := stdW) e ε t) →
    Sim (Rew.subst ![s] ▹ φ) (Rew.subst ![t] ▹ φ)

abbrev ReplaceHeadHyp (A : Semisentence LForm 2) (Sim : SimRel) : Prop :=
  ∀ {H : Set ThetaVNoteD → Set ThetaVNoteD}, ThetaVNoteD.IsOperator H →
    ∀ {α : ThetaVNoteD} {Γ : Sequent (LIinfW)} {φ φ' : Proposition (LIinfW)},
    IDwDerivable A ThetaVNoteD.zero H α (φ :: Γ) → Sim φ φ' →
    IDwDerivable A ThetaVNoteD.zero H α (φ' :: Γ)

/-! ### Terms under the embedding -/

section Terms

variable {ξ : Type*} {m : ℕ}

private lemma embT_numeral_zero :
    embT ((0 : ℕ) : Semiterm (LXJ) ξ m) = ((0 : ℕ) : Semiterm (LIinfW) ξ m) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, embedW, embedFuncW]
  rfl

private lemma embT_numeral_one :
    embT ((1 : ℕ) : Semiterm (LXJ) ξ m) = ((1 : ℕ) : Semiterm (LIinfW) ξ m) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, embedW, embedFuncW]
  rfl

theorem embT_add (v : Fin 2 → Semiterm (LXJ) ξ m) :
    embT (Semiterm.Operator.Add.add.operator v) =
      Semiterm.Operator.Add.add.operator (embT ∘ v) := by
  simp only [embT, Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func]
  refine congrArg (Semiterm.func (Language.Add.add : (LIinfW).Func 2)) ?_
  funext i
  rfl

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
    embT ((c : ℕ) : Semiterm (LXJ) ξ m) = ((c : ℕ) : Semiterm (LIinfW) ξ m) := by
  induction c with
  | zero => exact embT_numeral_zero
  | succ c ih =>
    cases c with
    | zero => exact embT_numeral_one
    | succ c =>
      rw [numeralX_succ_succ (LXJ) c, numeralX_succ_succ (LIinfW) c, embT_add]
      congr 1
      funext i
      match i with
      | ⟨0, _⟩ => exact ih
      | ⟨1, _⟩ => exact embT_numeral_one

end Terms

/-- The successor term `#0 + 1` of `(LXJ)`. -/
def sucX : Semiterm (LXJ) ℕ 1 := ‘(#0 + 1)’

/-- The successor term `#0 + 1` of `(LIinfW)`. -/
def sucI : Semiterm (LIinfW) ℕ 1 := ‘(#0 + 1)’

theorem embT_sucX : embT sucX = sucI := by
  rw [sucX, sucI]
  show embT (Semiterm.Operator.Add.add.operator ![#0, ((1 : ℕ) : Semiterm (LXJ) ℕ 1)]) = _
  rw [embT_add]
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => exact embT_numeral 1

/-- `+` in operator form is `+` in function form. -/
theorem add_operator_eq_func {m : ℕ} (a b : Semiterm (LIinfW) ℕ m) :
    Semiterm.Operator.Add.add.operator ![a, b]
      = Semiterm.func (Language.Add.add : (LIinfW).Func 2) ![a, b] := by
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func]
  exact congrArg (Semiterm.func (Language.Add.add : (LIinfW).Func 2))
    (by funext i; match i with
        | ⟨0, _⟩ => simp
        | ⟨1, _⟩ => simp)

theorem subst_sucI (t : SyntacticTerm (LIinfW)) :
    Rew.subst ![t] sucI =
      Semiterm.func (Language.Add.add : (LIinfW).Func 2) ![t, ((1 : ℕ) : SyntacticTerm (LIinfW))] := by
  rw [← add_operator_eq_func]
  simp [sucI]

/-- The successor term with a closed term substituted has the successor value. -/
theorem val_subst_sucI
    (t : SyntacticTerm (LIinfW))
    (e : Fin 0 → ℕ) (ε : ℕ → ℕ) :
    Semiterm.val (s := stdW) e ε (Rew.subst ![t] sucI) =
      Semiterm.val (s := stdW) e ε t + 1 := by
  rw [subst_sucI, Semiterm.val_func]
  change Semiterm.val (s := stdW) e ε t +
    Semiterm.val (s := stdW) e ε (numI 1) = _
  rw [val_numI]

theorem freeVariables_subst_sucI {t : SyntacticTerm (LIinfW)} (ht : t.freeVariables = ∅) :
    (Rew.subst ![t] sucI).freeVariables = ∅ := by
  rw [subst_sucI, Semiterm.freeVariables_func]
  ext x
  simp only [Finset.notMem_empty, iff_false, Finset.mem_biUnion, Finset.mem_univ, true_and,
    not_exists]
  intro i hx
  match i with
  | ⟨0, h⟩ =>
    have h0 : (![t, ((1 : ℕ) : SyntacticTerm (LIinfW))] : Fin 2 → SyntacticTerm (LIinfW)) ⟨0, h⟩ = t :=
      rfl
    rw [h0, ht] at hx
    exact Finset.notMem_empty x hx
  | ⟨1, h⟩ =>
    have h1 : (![t, ((1 : ℕ) : SyntacticTerm (LIinfW))] : Fin 2 → SyntacticTerm (LIinfW)) ⟨1, h⟩ =
        ((1 : ℕ) : SyntacticTerm (LIinfW)) := rfl
    rw [h1, numeral_freeVariables] at hx
    exact Finset.notMem_empty x hx

theorem OmegaTwo_mem_pa {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H)
    (X : Set ThetaVNoteD) (m : ℕ) :
    ThetaVNoteD.nadd OmegaTwo_pa (ThetaVNoteD.ofNat m) ∈ H X :=
  hH.nadd_mem (hH.nadd_mem hH.OmegaW_mem hH.OmegaW_mem) (hH.ofNat_mem m)

theorem Omega_le_OmegaTwo_nadd_pa (m : ℕ) :
    ThetaVNoteD.OmegaW ≤ ThetaVNoteD.nadd OmegaTwo_pa (ThetaVNoteD.ofNat m) :=
  le_trans (ThetaVNoteD.le_nadd_left _ _) (ThetaVNoteD.le_nadd_left _ _)

/-! ### The embedded induction axiom -/

section Induction

variable {H : Set ThetaVNoteD → Set ThetaVNoteD}

/-- The induction axiom for the body `ψ`, in `(LIinfW)`. -/
def succIndI (ψ : Semiformula (LIinfW) ℕ 1) : Proposition (LIinfW) :=
  (ψ/[numI 0]) 🡒 (∀¹ (ψ/[(#0 : Semiterm (LIinfW) ℕ 1)] 🡒 ψ/[sucI])) 🡒
    ∀¹ (ψ/[(#0 : Semiterm (LIinfW) ℕ 1)])

/-- The body of the existential that the negated induction step is. -/
def stepBody (ψ : Semiformula (LIinfW) ℕ 1) : Semiformula (LIinfW) ℕ 1 :=
  ψ/[(#0 : Semiterm (LIinfW) ℕ 1)] ⋏ ∼(ψ/[sucI])

theorem succInd_eq (φ : Semiformula (LXJ) ℕ 1) :
    succInd φ = (φ/[((0 : ℕ) : SyntacticTerm (LXJ))]) 🡒
      (∀¹ (φ/[(#0 : Semiterm (LXJ) ℕ 1)] 🡒 φ/[sucX])) 🡒 ∀¹ (φ/[(#0 : Semiterm (LXJ) ℕ 1)]) := rfl

theorem numSubst₁_subst (g : ℕ → ℕ) (s : Semiterm (LIinfW) ℕ 1) (φ : Semiformula (LIinfW) ℕ 1) :
    numSubst₁ g ▹ (φ/[s]) = (numSubst₁ g ▹ φ)/[numSubst₁ g s] := by
  simpa [← comp_app] using smul_ext' (φ := φ) <| by ext x <;> simp [Rew.comp_app, numSubst₁]

theorem numSubst₁_sucI (g : ℕ → ℕ) : numSubst₁ g (sucI : Semiterm (LIinfW) ℕ 1) = sucI := by
  simp [sucI, numSubst₁]

/-- **A numeral assignment passes through the embedded induction axiom.** -/
theorem numSubst_embK_succInd (g : ℕ → ℕ) (φ : Semiformula (LXJ) ℕ 1) :
    numSubst g ▹ embK (succInd φ) = succIndI (numSubst₁ g ▹ embK φ) := by
  rw [succInd_eq, succIndI]
  simp only [Semiformula.imp_eq, embK_or, embK_neg, embK_all, embK_subst₁, embT_numeral,
    embT_sucX, Semiterm.lMap_bvar, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, numSubst_all, numSubst_subst, rew_numeral]
  rw [numSubst₁_subst, numSubst₁_subst, numSubst₁_sucI, numSubst₁_bvar]

/-- Substituting into a substitution instance. -/
theorem subst_subst₁ (ψ : Semiformula (LIinfW) ℕ 1) (s : Semiterm (LIinfW) ℕ 1)
    (t : SyntacticTerm (LIinfW)) : (ψ/[s])/[t] = ψ/[Rew.subst ![t] s] := by
  simpa [← comp_app] using smul_ext' (φ := ψ) <| by ext x <;> simp [Rew.comp_app]

theorem subst_bvar_subst (ψ : Semiformula (LIinfW) ℕ 1) (t : SyntacticTerm (LIinfW)) :
    (ψ/[(#0 : Semiterm (LIinfW) ℕ 1)])/[t] = ψ/[t] := by
  rw [subst_subst₁]; simp

theorem stepBody_inst (ψ : Semiformula (LIinfW) ℕ 1) (m : ℕ) :
    (stepBody ψ)/[numI m] = ψ/[numI m] ⋏ ∼(ψ/[Rew.subst ![numI m] sucI]) := by
  show (Rew.subst ![numI m]) ▹ (ψ/[(#0 : Semiterm (LIinfW) ℕ 1)] ⋏ ∼(ψ/[sucI])) = _
  rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg]
  congr 1
  · exact subst_bvar_subst ψ _
  · exact congrArg _ (subst_subst₁ ψ _ _)

theorem neg_step (ψ : Semiformula (LIinfW) ℕ 1) :
    ∼(∀¹ (ψ/[(#0 : Semiterm (LIinfW) ℕ 1)] 🡒 ψ/[sucI])) = ∃¹ stepBody ψ := by
  simp [stepBody, Semiformula.imp_eq]

/-- **The chain** (first lecture, proof of Theorem 3.7): from `¬ψ(0)`, the negated induction
step and `ψ(m̄)` in the sequent, a cut-free derivation of height `ω · rk ψ ⊕ 2m`. -/
theorem chain (taut : TautHyp A)
    (Sim : SimRel) (sim_subst_closed : SimSubstClosedHyp Sim)
    (replace_head : ReplaceHeadHyp A Sim)
    (hH : ThetaVNoteD.NiceS H) (ψ : Semiformula (LIinfW) ℕ 1)
    (hf : ψ.freeVariables = ∅) (hX : XFreeI ψ) (hp : paramsAt ψ ⊆ H ∅) :
    ∀ (m : ℕ) (Γ : Sequent (LIinfW)), ∼(ψ/[numI 0]) ∈ Γ → (∃¹ stepBody ψ) ∈ Γ →
      ψ/[numI m] ∈ Γ → paramsVal Γ ⊆ H ∅ →
      IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk ψ)) (ThetaVNoteD.ofNat (2 * m))) Γ := by
  have hK : ∀ t : SyntacticTerm (LIinfW), ThetaVNoteD.adjoin H (paramsAt (ψ/[t])) = H := fun t =>
    ThetaVNoteD.adjoin_eq_self hH.1 (paramsAt_subst_sub hp t)
  have hrk : ∀ t : SyntacticTerm (LIinfW), rk (ψ/[t]) = rk ψ := fun t => rk_subst ψ t
  have hmem : ∀ c : ℕ, ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk ψ)) (ThetaVNoteD.ofNat c) ∈ H ∅ :=
    fun c => hH.nadd_mem (hH.omegaMul_mem (rk_mem_pa hH _ (fun s hs => hp ⟨s, hs, rfl⟩))) (hH.ofNat_mem c)
  have taut' : ∀ t : SyntacticTerm (LIinfW), t.freeVariables = ∅ →
      IDwDerivable A ThetaVNoteD.zero H (ThetaVNoteD.omegaMul (rk ψ)) [ψ/[t], ∼(ψ/[t])] := by
    intro t ht
    have d := taut hH (ψ/[t]) (freeVariables_subst_of_closed_pa ψ hf ht)
    rwa [hK t, hrk t] at d
  intro m
  induction m with
  | zero =>
    intro Γ h0 _ hn hP
    rw [Nat.mul_zero, ThetaVNoteD.ofNat_zero, ThetaVNoteD.nadd_zero]
    refine (taut' (numI 0) (numI_freeVariables 0)).weaken_seq hH.1 ?_ hP
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hn
    · exact h0
  | succ m ih =>
    intro Γ h0 hS hn hP
    set inst : Proposition (LIinfW) := (stepBody ψ)/[numI m] with hinst
    have hinst' : inst = ψ/[numI m] ⋏ ∼(ψ/[Rew.subst ![numI m] sucI]) := stepBody_inst ψ m
    have pinst : paramsAt inst ⊆ H ∅ := by rw [hinst, paramsAt_subst, stepBody, paramsAt_and,
      paramsAt_neg, paramsAt_subst, paramsAt_subst, Set.union_self]; exact hp
    have hP1 : paramsVal (inst :: Γ) ⊆ H ∅ := by
      rw [paramsVal_cons]; exact Set.union_subset pinst hP
    have hP2 : ∀ χ : Proposition (LIinfW), paramsAt χ ⊆ H ∅ → paramsVal (χ :: inst :: Γ) ⊆ H ∅ := by
      intro χ hχ; rw [paramsVal_cons]; exact Set.union_subset hχ hP1
    -- the left conjunct, from the chain for `m`
    have d1 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk ψ)) (ThetaVNoteD.ofNat (2 * m)))
        (ψ/[numI m] :: inst :: Γ) :=
      ih _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h0))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hS)) List.mem_cons_self
        (hP2 _ (paramsAt_subst_sub hp _))
    -- the right conjunct, from Lemma 6.1 at the numeral `(m+1)‾` and term replacement
    have hsuc : (Rew.subst ![numI m] sucI).freeVariables = ∅ :=
      freeVariables_subst_sucI (t := numI m) (numI_freeVariables m)
    have d2' : IDwDerivable A ThetaVNoteD.zero H (ThetaVNoteD.omegaMul (rk ψ))
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
    have d2 : IDwDerivable A ThetaVNoteD.zero H (ThetaVNoteD.omegaMul (rk ψ))
        (∼(ψ/[Rew.subst ![numI m] sucI]) :: inst :: Γ) :=
      replace_head hH.1 d2' hsim
    have hlt1 : ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk ψ)) (ThetaVNoteD.ofNat (2 * m)) <
        ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk ψ)) (ThetaVNoteD.ofNat (2 * m + 1)) :=
      ThetaVNoteD.nadd_ofNat_lt_nadd_ofNat_pa _ (by omega)
    have hlt2 : ThetaVNoteD.omegaMul (rk ψ) <
        ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk ψ)) (ThetaVNoteD.ofNat (2 * m + 1)) :=
      ThetaVNoteD.lt_nadd_ofNat_succ_pa _ _
    have d3 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk ψ)) (ThetaVNoteD.ofNat (2 * m + 1)))
        (inst :: Γ) :=
      .and (hmem _) hP1 (by rw [← hinst']; exact List.mem_cons_self) hlt1 hlt2 d1 d2
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
    exact .exs m (hmem _) hP hS (lt_of_lt_of_le (ThetaVNoteD.ofNat_lt_ofNat (by omega))
      (ThetaVNoteD.le_nadd_right _ _)) (ThetaVNoteD.nadd_ofNat_lt_nadd_ofNat_pa _ (by omega)) d3

/-- **The induction axiom for a body without free variables**, cut-free, at height
`ω · rk ψ ⊕ ω ⊕ 4`. -/
theorem succIndI_derivable (taut : TautHyp A)
    (Sim : SimRel) (sim_subst_closed : SimSubstClosedHyp Sim)
    (replace_head : ReplaceHeadHyp A Sim)
    (hH : ThetaVNoteD.NiceS H) (ψ : Semiformula (LIinfW) ℕ 1)
    (hf : ψ.freeVariables = ∅) (hX : XFreeI ψ) (hp : paramsAt ψ ⊆ H ∅) :
    IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk ψ)) omegaT_pa) (ThetaVNoteD.ofNat 4))
      [succIndI ψ] := by
  set hω : ThetaVNoteD := ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk ψ)) omegaT_pa with hhω
  have hmem : ∀ c : ℕ, ThetaVNoteD.nadd hω (ThetaVNoteD.ofNat c) ∈ H ∅ := fun c =>
    hH.nadd_mem (hH.nadd_mem (hH.omegaMul_mem (rk_mem_pa hH _ (fun s hs => hp ⟨s, hs, rfl⟩))) (hH.omegaPow_mem hH.one_mem))
      (hH.ofNat_mem c)
  have hlt : ∀ j c : ℕ, j < c → ThetaVNoteD.nadd hω (ThetaVNoteD.ofNat j) <
      ThetaVNoteD.nadd hω (ThetaVNoteD.ofNat c) := fun j c h => ThetaVNoteD.nadd_ofNat_lt_nadd_ofNat_pa _ h
  have h0 : ThetaVNoteD.nadd hω (ThetaVNoteD.ofNat 0) = hω := by
    rw [ThetaVNoteD.ofNat_zero, ThetaVNoteD.nadd_zero]
  have hone : ∀ c, ThetaVNoteD.one < ThetaVNoteD.nadd hω (ThetaVNoteD.ofNat c) := fun c =>
    lt_of_lt_of_le (by rw [← ThetaVNoteD.ofNat_one]; exact ofNat_lt_omegaT 1)
      (le_trans (ThetaVNoteD.le_nadd_right _ _) (ThetaVNoteD.le_nadd_left _ _))
  set Z : Proposition (LIinfW) := ∼(ψ/[numI 0]) with hZ
  set S : Proposition (LIinfW) := ∃¹ stepBody ψ with hS
  set U : Proposition (LIinfW) := ∀¹ (ψ/[(#0 : Semiterm (LIinfW) ℕ 1)]) with hU
  have eM : succIndI ψ = Z ⋎ (S ⋎ U) := by
    rw [succIndI, Semiformula.imp_eq, Semiformula.imp_eq, neg_step]
  have pZ : paramsAt Z ⊆ H ∅ := by rw [hZ, paramsAt_neg]; exact paramsAt_subst_sub hp _
  have pS : paramsAt S ⊆ H ∅ := by
    rw [hS, paramsAt_exs, stepBody, paramsAt_and, paramsAt_neg, paramsAt_subst, paramsAt_subst,
      Set.union_self]; exact hp
  have pU : paramsAt U ⊆ H ∅ := by rw [hU, paramsAt_all]; exact paramsAt_subst_sub hp _
  have pM : paramsAt (succIndI ψ) ⊆ H ∅ := by
    rw [eM, paramsAt_or, paramsAt_or]; exact Set.union_subset pZ (Set.union_subset pS pU)
  have pl : ∀ Γ : Sequent (LIinfW), (∀ χ ∈ Γ, paramsAt χ ⊆ H ∅) → paramsVal Γ ⊆ H ∅ := by
    intro Γ h
    induction Γ with
    | nil => simp [paramsVal]
    | cons φ Γ ihΓ =>
      rw [paramsVal_cons]
      exact Set.union_subset (h φ List.mem_cons_self) (ihΓ fun χ hχ => h χ (List.mem_cons_of_mem _ hχ))
  -- the ω-rule
  have dω : IDwDerivable A ThetaVNoteD.zero H hω [U, Z, S, S ⋎ U, succIndI ψ] := by
    refine .all (fun m => ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk ψ))
      (ThetaVNoteD.ofNat (2 * m))) (by rw [← h0]; exact hmem 0) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl | rfl | rfl
        · exact pU
        · exact pZ
        · exact pS
        · rw [paramsAt_or]; exact Set.union_subset pS pU
        · exact pM)) List.mem_cons_self
      (fun m => ThetaVNoteD.nadd_lt_nadd_right _ (ofNat_lt_omegaT _)) (fun m => ?_)
    rw [subst_bvar_subst]
    refine chain taut Sim sim_subst_closed replace_head hH ψ hf hX hp m _ ?_ ?_
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
  have d1 : IDwDerivable A ThetaVNoteD.zero H (ThetaVNoteD.nadd hω (ThetaVNoteD.ofNat 1))
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
      (ThetaVNoteD.lt_nadd_ofNat_succ_pa hω 0) dω
  have d2 : IDwDerivable A ThetaVNoteD.zero H (ThetaVNoteD.nadd hω (ThetaVNoteD.ofNat 2))
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
  have d3 : IDwDerivable A ThetaVNoteD.zero H (ThetaVNoteD.nadd hω (ThetaVNoteD.ofNat 3))
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

/-- **Every atom rank is `⪯ Ω_ω`**: stage atoms sit at `⪯ Ω_j ≺ Ω_ω`, `Jlev ↑j` at `Ω_j + 1 ≺ Ω_ω`,
`Jlev ⊤` at exactly `Ω_ω` (the replacement, for `IDw`, of the `IDn` proof that went through
`rk_le_add_ofNat`, which is not stated for `IDw`, see `IDw.Rank`). -/
theorem atomRk_le_OmegaW_pa {k : ℕ} (r : LIinfW.Rel k) : atomRk r ≤ ThetaVNoteD.OmegaW := by
  rcases r with r | r
  · exact ThetaVNoteD.zero_le' _
  · cases r with
    | X => exact ThetaVNoteD.zero_le' _
    | stage s =>
      obtain ⟨j, b⟩ := s
      exact le_trans (atomRkStage_mk_le_Omega j b) (le_of_lt (ThetaVNoteD.Omega_lt_OmegaW j))
    | jlev ℓ =>
      induction ℓ using WithTop.recTopCoe with
      | top => exact le_refl _
      | coe j =>
        exact le_of_lt (ThetaVNoteD.succ_lt_prin trivial (ThetaVNoteD.OmegaBelow_lt_OmegaW j))

/-- **`rk φ ⪯ Ω_n ⊕ ω · c`**, `c` the complexity of `φ` — every parameter of `φ` is some
level's own top `Ω_{j+1} ≤ Ω_n`, so `IDw.Rank.rk_le_add_ofNat` applies unconditionally. The
`IDw` analogue of `ID1.Rank.rk_le_Omega_nadd`. -/
theorem rk_le_Omega_nadd {ξ : Type*} {m : ℕ} (φ : Semiformula (LIinfW) ξ m) :
    rk φ ≤ ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat φ.complexity) := by
  rw [← ThetaVNoteD.add_ofNat_eq_nadd]
  induction φ using Semiformula.rec' with
  | hverum => rw [rk_verum]; exact ThetaVNoteD.zero_le' _
  | hfalsum => rw [rk_falsum]; exact ThetaVNoteD.zero_le' _
  | hrel r v =>
    rw [rk_rel]; exact le_trans (atomRk_le_OmegaW_pa r) (ThetaVNoteD.le_add_right _ _)
  | hnrel r v =>
    rw [rk_nrel]; exact le_trans (atomRk_le_OmegaW_pa r) (ThetaVNoteD.le_add_right _ _)
  | hand φ ψ ihφ ihψ =>
    rw [rk_and, Semiformula.complexity_and, ← ThetaVNoteD.succ_add_ofNat]
    refine ThetaVNoteD.succ_le_succ (max_le ?_ ?_)
    · exact le_trans ihφ (ThetaVNoteD.add_le_add_left _ (ThetaVNoteD.ofNat_le_ofNat (le_max_left _ _)))
    · exact le_trans ihψ (ThetaVNoteD.add_le_add_left _ (ThetaVNoteD.ofNat_le_ofNat (le_max_right _ _)))
  | hor φ ψ ihφ ihψ =>
    rw [rk_or, Semiformula.complexity_or, ← ThetaVNoteD.succ_add_ofNat]
    refine ThetaVNoteD.succ_le_succ (max_le ?_ ?_)
    · exact le_trans ihφ (ThetaVNoteD.add_le_add_left _ (ThetaVNoteD.ofNat_le_ofNat (le_max_left _ _)))
    · exact le_trans ihψ (ThetaVNoteD.add_le_add_left _ (ThetaVNoteD.ofNat_le_ofNat (le_max_right _ _)))
  | hall φ ih =>
    rw [rk_all, Semiformula.complexity_all, ← ThetaVNoteD.succ_add_ofNat]
    exact ThetaVNoteD.succ_le_succ ih
  | hexs φ ih =>
    rw [rk_exs, Semiformula.complexity_exs, ← ThetaVNoteD.succ_add_ofNat]
    exact ThetaVNoteD.succ_le_succ ih

/-- `ω · rk φ ⪯ Ω_n ⊕ ω · c`, `c` the complexity of `φ`. -/
theorem omegaMul_rk_le {ξ : Type*} {m : ℕ} (φ : Semiformula (LIinfW) ξ m) :
    ThetaVNoteD.omegaMul (rk φ) ≤
      ThetaVNoteD.nadd ThetaVNoteD.OmegaW
        (ThetaVNoteD.omegaMul (ThetaVNoteD.ofNat φ.complexity)) := by
  rw [← ThetaVNoteD.omegaMul_OmegaW, ← ThetaVNoteD.omegaMul_nadd]
  exact ThetaVNoteD.omegaMul_le_omegaMul (rk_le_Omega_nadd φ)

theorem omegaMul_ofNat_lt_Omega (c : ℕ) :
    ThetaVNoteD.omegaMul (ThetaVNoteD.ofNat c) < ThetaVNoteD.OmegaW :=
  ThetaVNoteD.omegaMul_lt_prin trivial (ThetaVNoteD.ofNat_lt_prin (p := ThetaVNoteD.OmegaW) trivial c)

/-- `Ω_n ⊕ y ⪯ Ω_n · 2` for `y ≺ Ω_n`. -/
theorem nadd_Omega_le_OmegaTwo {y : ThetaVNoteD} (hy : y < ThetaVNoteD.OmegaW) (m : ℕ) :
    ThetaVNoteD.nadd ThetaVNoteD.OmegaW y ≤
      ThetaVNoteD.nadd OmegaTwo_pa (ThetaVNoteD.ofNat m) :=
  le_trans (ThetaVNoteD.nadd_le_nadd_right _ (le_of_lt hy)) (ThetaVNoteD.le_nadd_left _ _)

end Bounds

/-! ### The induction axioms -/

section InductionAxiom

/-- Numerals of `(LXJ)`. -/
abbrev numX (m : ℕ) : SyntacticTerm (LXJ) := Semiterm.numeral m

theorem embK_rewrite_numX (g : ℕ → ℕ) (ψ : Proposition (LXJ)) :
    embK (Rew.rewrite (fun x => numX (g x)) ▹ ψ) = numSubst g ▹ embK ψ := by
  rw [embK, killX_rew, embed, Semiformula.lMap_rewrite, embK, embed, numSubst]
  have e : (Semiterm.lMap embedW ∘ fun x => (numX (g x) : SyntacticTerm (LXJ))) =
      fun x => (numI (g x) : SyntacticTerm (LIinfW)) := by
    funext x
    show embT (numX (g x)) = numI (g x)
    exact embT_numeral (g x)
  rw [e]

theorem emb_embK_univCl (ψ : Proposition (LXJ)) :
    (Rewriting.emb (embK (Semiformula.univCl ψ)) : Proposition (LIinfW)) =
      ∀¹* (embK (Rew.fixitr 0 ψ.fvSup ▹ ψ)) := by
  rw [← embK_emb, Semiformula.coe_univCl_eq_univCl', Semiformula.univCl', embK_allClosure]

theorem embK_fixitr_inst (ψ : Proposition (LXJ)) (w : Fin (0 + ψ.fvSup) → ℕ) :
    (embK (Rew.fixitr 0 ψ.fvSup ▹ ψ) ⇜ fun i => numI (w i)) =
      numSubst (fun y => if hy : y < 0 + ψ.fvSup then w ⟨y, hy⟩ else 0) ▹ embK ψ := by
  have e1 : (fun i : Fin (0 + ψ.fvSup) => (numI (w i) : SyntacticTerm (LIinfW))) =
      embT ∘ (fun i : Fin (0 + ψ.fvSup) => (numX (w i) : SyntacticTerm (LXJ))) := by
    funext i
    exact (embT_numeral (w i)).symm
  rw [e1, ← embK_subst, ← embK_rewrite_numX]
  congr 1
  have e2 : (fun i : Fin (0 + ψ.fvSup) => (numX (w i) : SyntacticTerm (LXJ))) =
      fun i : Fin (0 + ψ.fvSup) =>
        (fun y : ℕ => (numX (if hy : y < 0 + ψ.fvSup then w ⟨y, hy⟩ else 0) : SyntacticTerm (LXJ)))
          (i : ℕ) := by
    funext i
    simp only [dif_pos i.isLt, Fin.eta]
  rw [e2]
  exact Semiformula.subst_comp_fixitr_eq_map ψ
    (fun y => numX (if hy : y < 0 + ψ.fvSup then w ⟨y, hy⟩ else 0))

/-- **Every induction axiom of `paLXIN (ℕ)`** (Freund, proof of Theorem 6.5, after Theorem
3.7 of the first lecture): cut-free, at a height below `Ω_n · 2`. -/
theorem induction_axiom (taut : TautHyp A)
    (Sim : SimRel) (sim_subst_closed : SimSubstClosedHyp Sim)
    (replace_head : ReplaceHeadHyp A Sim)
    (axDerivable_of_le : AxDerivableOfLeHyp A AxDerivable)
    (allClosure_derivable : AllClosureDerivableHyp A) {σ : Sentence (LXJ)}
    (h : σ ∈ InductionScheme (LXJ) Set.univ) : AxDerivable A σ := by
  obtain ⟨φ, -, rfl⟩ := h
  set ψ0 : Proposition (LXJ) := succInd φ with hψ0
  set β : ThetaVNoteD := ThetaVNoteD.nadd (ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk (embK φ))) omegaT_pa)
    (ThetaVNoteD.ofNat 4) with hβ
  refine axDerivable_of_le (0 + ψ0.fvSup)
    (ThetaVNoteD.nadd β (ThetaVNoteD.ofNat (0 + ψ0.fvSup))) ?_ (fun H hH => ?_)
  · have h1 : β ≤ ThetaVNoteD.nadd (ThetaVNoteD.nadd (ThetaVNoteD.nadd ThetaVNoteD.OmegaW
        (ThetaVNoteD.omegaMul (ThetaVNoteD.ofNat (embK φ).complexity))) omegaT_pa) (ThetaVNoteD.ofNat 4) :=
      ThetaVNoteD.nadd_le_nadd_left' _ (ThetaVNoteD.nadd_le_nadd_left' _ (omegaMul_rk_le _))
    refine le_trans (ThetaVNoteD.nadd_le_nadd_left' _ h1) ?_
    rw [ThetaVNoteD.nadd_assoc, ThetaVNoteD.nadd_assoc, ThetaVNoteD.nadd_assoc]
    refine nadd_Omega_le_OmegaTwo ?_ _
    exact ThetaVNoteD.nadd_lt_prin trivial (omegaMul_ofNat_lt_Omega _)
      (ThetaVNoteD.nadd_lt_prin trivial (ThetaVNoteD.omegaPow_lt_prin trivial
        (ThetaVNoteD.one_lt_prin (p := ThetaVNoteD.OmegaW) trivial))
        (ThetaVNoteD.nadd_lt_prin trivial (ThetaVNoteD.ofNat_lt_prin (p := ThetaVNoteD.OmegaW) trivial _)
          (ThetaVNoteD.ofNat_lt_prin (p := ThetaVNoteD.OmegaW) trivial _)))
  · have hpK : ∀ {m : ℕ} (χ : Semiformula (LXJ) ℕ m), paramsAt (embK χ) ⊆ H ∅ :=
      fun χ => paramsAt_embK hH χ
    rw [emb_embK_univCl]
    refine allClosure_derivable hH.1 _ (fun j => hH.nadd_mem (hH.nadd_mem
      (hH.nadd_mem (hH.omegaMul_mem (rk_mem_pa hH _ (fun s hs => hpK φ ⟨s, hs, rfl⟩))) (hH.omegaPow_mem hH.one_mem))
      (hH.ofNat_mem 4)) (hH.ofNat_mem j)) (hpK (Rew.fixitr 0 ψ0.fvSup ▹ ψ0)) (fun w => ?_)
    rw [embK_fixitr_inst, numSubst_embK_succInd]
    set g : ℕ → ℕ := fun y => if hy : y < 0 + ψ0.fvSup then w ⟨y, hy⟩ else 0 with hg
    have d := succIndI_derivable taut Sim sim_subst_closed replace_head hH
      (numSubst₁ g ▹ embK φ) (freeVariables_numSubst₁ g _)
      ((xFreeI_rew (numSubst₁ g) _).mpr (xFreeI_embK φ)) (by rw [paramsAt_rew]; exact hpK φ)
    rwa [rk_rew] at d

end InductionAxiom

end IDw

end OrdinalAnalysis
