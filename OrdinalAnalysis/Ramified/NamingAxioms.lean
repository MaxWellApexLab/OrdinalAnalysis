/-
  Every naming axiom of `RA_∞` is cut-free derivable, and its rank is below the
  level it names.

  `Theory.lean` supplies two one-sided implications per code `a`:

      nameOut a := ∀¹ (nmemAt (lvl a) #0 (nameTerm a) ⋎ body a)   "everything named by `a` satisfies its body"
      nameIn  a := ∀¹ (∼(body a) ⋎ memAt (lvl a) #0 (nameTerm a))  "everything satisfying the body is named by `a`"

  closed by `Semiformula.univCl` into sentences of `LRA`.  This file shows that
  `RA_∞ ⊢^0_β evR (emb (univCl (nameOut a)))` for some finite `β`, and likewise
  for `nameIn a` — cut-free, because unfolding a name costs nothing but an
  ω-rule and a single (Pr)/(Pr⁻) inference — and that the rank of the evaluated,
  embedded axiom is below `ω^{lvl a}`.  Together with `Gentzen/CutAxioms.lean`'s
  generic `cut_axioms_of` (ported here as `CutAxioms.cut_axioms_of`), this is
  what lets the naming schema of `RA Λ` be cut away level by level.

  ## The route

  **Closing a variable-free proposition changes nothing.**  Under `ParamFree a`
  the body `body a` has no free variable, and a short computation
  (`freeVariables_nameOut`, `freeVariables_nameIn`) shows `nameOut a` and
  `nameIn a` inherit this: the only term that could carry a free variable is
  `nameTerm a`, a numeral, and `#0` is bound, not free.  So `univCl` adds no
  quantifier — Foundation's own `Semiformula.univCl'_eq_self_of` says a
  variable-free `univCl'` is the identity, and `Semiformula.emb_toEmpty` then
  says embedding undoes `toEmpty` — and `Rewriting.emb (univCl φ) = φ`
  (`emb_univCl_of_freeVariables_eq_empty`) is the whole of what closing costs
  here.

  **Evaluating the naming matrix.**  `evR` fixes the set atom
  `nmemAt (lvl a) #0 (nameTerm a)` (both arguments are already numerals or the
  bound variable `#0`, so `evTR` does not move them) and otherwise pushes
  inside, leaving `evR (body a)` as the only place a genuine evaluation can
  occur (`ev_nameOut`, `ev_nameIn`).  Instantiating the resulting ω-quantifier
  at a numeral `n` and evaluating again reduces, by the congruence law
  `evInstR_inst_ev` of `Evaluate.lean`, to *the* `n`-th instance of the body
  sitting next to the `n`-th instance of the atom
  (`evInstR_inst_nameOutBody`, `evInstR_inst_nameInBody`) — exactly the
  premise shape the (Pr)/(Pr⁻) rules of `Calculus.lean` were built to consume.

  **Deriving the instance.**  `OmegaDerivableR` has identity only for atoms;
  `OmegaDerivableR.identity_formula` extends it to an arbitrary formula by the
  same induction `Omega/Identity.lean` uses for the unramified calculus, at the
  finite height `2 · complexity`.  One (Pr⁻) (for `nameOut`) or (Pr) (for
  `nameIn`) inference against that identity sequent, followed by one `or`, both
  at heights that do not depend on `n` because `InstantiationR` preserves
  complexity, gives the `n`-th instance at a height uniform in `n` — so the
  outer ω-rule needs no growing family of premise ordinals, unlike the
  induction schema of `Gentzen/AxiomsInduction.lean`. Heights stay in a generic
  `[OrdinalNotation O]`; only finitely many `OrdinalNotation.ofNat` values are
  ever used.

  **The rank bound.**  `lvlOf (nameOut a) = lvlOf (nameIn a) = lvl a`
  (`Theory.lean`'s `lvlOf_nameOut`/`lvlOf_nameIn`, under `Good a`), `evR`
  preserves the level (`lvlOf_evR`), and `Rank.lean`'s
  `rank_lt_omegaPow_of_level` turns "level below `ν`" into "rank below `ω^ν`" —
  so a naming axiom at a level below `ν` has rank below `ω^ν`, which is what
  the level-by-level cut-elimination climb needs from the schema `NamingAxioms
  {μ | μ < ν}`.
-/
import OrdinalAnalysis.Ramified.Theory
import OrdinalAnalysis.Ramified.Evaluate

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Derivation

/-! ### Closing a variable-free proposition is the identity

`Semiformula.univCl φ := φ.univCl'.toEmpty _`, and Foundation already proves
both halves of the round trip: `Semiformula.emb_toEmpty` undoes `toEmpty`, and
`Semiformula.univCl'_eq_self_of` says `univCl'` does nothing to a formula with
no free variable (its closure block `∀¹*` is empty). -/

/-- **Closing a variable-free proposition and embedding it back gives the
proposition itself.**  The naming axioms use this to shed the `univCl` the
theory needs (a `Sentence`) but the calculus does not (a `Proposition`). -/
theorem emb_univCl_of_freeVariables_eq_empty {φ : Proposition LRA} (h : φ.freeVariables = ∅) :
    (Rewriting.emb (Semiformula.univCl φ) : Proposition LRA) = φ := by
  rw [Semiformula.coe_univCl_eq_univCl', Semiformula.univCl'_eq_self_of φ h]

/-! ### The naming matrices are variable-free under `ParamFree`

Neither `#0` (bound, not free) nor `nameTerm a` (a numeral) carries a free
variable, so the only source of one in `nameOut a`/`nameIn a` is `body a`
itself. -/

theorem freeVariables_memAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    (memAt ν t s).freeVariables = t.freeVariables ∪ s.freeVariables := by
  have h := Semiformula.freeVariables_rel (Sum.inr (RARel.mem ν) : LRA.Rel 2)
    (![t, s] : Fin 2 → Semiterm LRA ℕ n)
  refine h.trans ?_
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (by simpa using hi)
    · exact Or.inr (by simpa using hi)
  · rintro (h | h)
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩

theorem freeVariables_nmemAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    (nmemAt ν t s).freeVariables = t.freeVariables ∪ s.freeVariables := by
  have h := Semiformula.freeVariables_nrel (Sum.inr (RARel.mem ν) : LRA.Rel 2)
    (![t, s] : Fin 2 → Semiterm LRA ℕ n)
  refine h.trans ?_
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (by simpa using hi)
    · exact Or.inr (by simpa using hi)
  · rintro (h | h)
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩

/-- The name of a code is a numeral, hence variable-free. -/
theorem freeVariables_nameTerm (a : ℕ) : (nameTerm a : Semiterm LRA ℕ 1).freeVariables = ∅ :=
  freeVariables_of_groundR (groundR_numAtR a)

/-- **`nameOut a` is variable-free whenever its code is parameter-free.** -/
theorem freeVariables_nameOut {a : ℕ} (hp : ParamFree a) : (nameOut a).freeVariables = ∅ := by
  have hbody : (body a).freeVariables = ∅ := hp
  unfold nameOut
  rw [Semiformula.freeVariables_all, Semiformula.freeVariables_or, freeVariables_nmemAt,
    freeVariables_nameTerm, hbody]
  simp

/-- **`nameIn a` is variable-free whenever its code is parameter-free.** -/
theorem freeVariables_nameIn {a : ℕ} (hp : ParamFree a) : (nameIn a).freeVariables = ∅ := by
  have hbody : (body a).freeVariables = ∅ := hp
  unfold nameIn
  rw [Semiformula.freeVariables_all, Semiformula.freeVariables_or, Semiformula.freeVariables_not,
    hbody, freeVariables_memAt, freeVariables_nameTerm]
  simp

/-! ### Substituting the subject into the naming matrix -/

/-- Substituting a term for the bound subject of the naming matrix's set atom
touches only the subject: the name `nameTerm a` is a numeral, so every
rewriting fixes it. -/
theorem subst_nmemAt_bvar0 {n : ℕ} (ν : Lv) (a : ℕ) (t : Semiterm LRA ℕ n) :
    (nmemAt ν (#0 : Semiterm LRA ℕ 1) (nameTerm a))/[t] = nmemAt ν t (numAtR a) := by
  have h := Semiformula.rew_nrel2 (Rew.subst ![t]) (r := (Sum.inr (RARel.mem ν) : LRA.Rel 2))
    (t₁ := (#0 : Semiterm LRA ℕ 1)) (t₂ := nameTerm a)
  have hfun : (fun i => (![(Rew.subst ![t] : Rew LRA ℕ 1 ℕ n) (#0 : Semiterm LRA ℕ 1),
        (Rew.subst ![t] : Rew LRA ℕ 1 ℕ n) (nameTerm a)] : Fin 2 → Semiterm LRA ℕ n) i)
      = (![t, numAtR a] : Fin 2 → Semiterm LRA ℕ n) := by
    funext i
    fin_cases i
    · rfl
    · exact rew_numAtR _ a
  have h2 : Semiformula.nrel (Sum.inr (RARel.mem ν) : LRA.Rel 2)
        ![(Rew.subst ![t] : Rew LRA ℕ 1 ℕ n) (#0 : Semiterm LRA ℕ 1),
          (Rew.subst ![t] : Rew LRA ℕ 1 ℕ n) (nameTerm a)]
      = nmemAt ν t (numAtR a) :=
    congrArg (Semiformula.nrel (Sum.inr (RARel.mem ν) : LRA.Rel 2)) hfun
  exact h.trans h2

/-- The dual, for the positive atom `nameIn` substitutes into. -/
theorem subst_memAt_bvar0 {n : ℕ} (ν : Lv) (a : ℕ) (t : Semiterm LRA ℕ n) :
    (memAt ν (#0 : Semiterm LRA ℕ 1) (nameTerm a))/[t] = memAt ν t (numAtR a) := by
  have h := Semiformula.rew_rel2 (Rew.subst ![t]) (r := (Sum.inr (RARel.mem ν) : LRA.Rel 2))
    (t₁ := (#0 : Semiterm LRA ℕ 1)) (t₂ := nameTerm a)
  have hfun : (fun i => (![(Rew.subst ![t] : Rew LRA ℕ 1 ℕ n) (#0 : Semiterm LRA ℕ 1),
        (Rew.subst ![t] : Rew LRA ℕ 1 ℕ n) (nameTerm a)] : Fin 2 → Semiterm LRA ℕ n) i)
      = (![t, numAtR a] : Fin 2 → Semiterm LRA ℕ n) := by
    funext i
    fin_cases i
    · rfl
    · exact rew_numAtR _ a
  have h2 : Semiformula.rel (Sum.inr (RARel.mem ν) : LRA.Rel 2)
        ![(Rew.subst ![t] : Rew LRA ℕ 1 ℕ n) (#0 : Semiterm LRA ℕ 1),
          (Rew.subst ![t] : Rew LRA ℕ 1 ℕ n) (nameTerm a)]
      = memAt ν t (numAtR a) :=
    congrArg (Semiformula.rel (Sum.inr (RARel.mem ν) : LRA.Rel 2)) hfun
  exact h.trans h2

/-! ### Evaluating the naming matrices

`evR` is a fixed point on the set atom of the matrix — both of its arguments
are already a bound variable or a numeral — so evaluating `nameOut a`/`nameIn
a` only ever touches `body a`. -/

theorem ev_nmemAt_bvar0 (a : ℕ) :
    evR (nmemAt (lvl a) (#0 : Semiterm LRA ℕ 1) (nameTerm a))
      = nmemAt (lvl a) (#0 : Semiterm LRA ℕ 1) (nameTerm a) := by
  rw [evR_nmemAt, evTR_bvar]
  exact congrArg (nmemAt (lvl a) (#0 : Semiterm LRA ℕ 1)) (evTR_numAtR a)

theorem ev_memAt_bvar0 (a : ℕ) :
    evR (memAt (lvl a) (#0 : Semiterm LRA ℕ 1) (nameTerm a))
      = memAt (lvl a) (#0 : Semiterm LRA ℕ 1) (nameTerm a) := by
  rw [evR_memAt, evTR_bvar]
  exact congrArg (memAt (lvl a) (#0 : Semiterm LRA ℕ 1)) (evTR_numAtR a)

/-- **`evR` of `nameOut a`**: the set atom is untouched, `body a` is evaluated. -/
theorem ev_nameOut (a : ℕ) :
    evR (nameOut a) = ∀¹ (nmemAt (lvl a) (#0 : Semiterm LRA ℕ 1) (nameTerm a) ⋎ evR (body a)) := by
  unfold nameOut
  rw [evR_all, evR_or, ev_nmemAt_bvar0]

/-- **`evR` of `nameIn a`**: dually. -/
theorem ev_nameIn (a : ℕ) :
    evR (nameIn a) = ∀¹ (∼(evR (body a)) ⋎ memAt (lvl a) (#0 : Semiterm LRA ℕ 1) (nameTerm a)) := by
  unfold nameIn
  rw [evR_all, evR_or, ev_memAt_bvar0, evR_neg]

/-! ### The `n`-th instance of the evaluated matrix

The congruence law `evInstR_inst_ev` says evaluating the body before or after
substituting a numeral instance gives the same result; combined with the fact
that `evR` fixes a set atom already between numerals, the `n`-th instance of
the evaluated matrix is exactly the (Pr)/(Pr⁻) premise shape. -/

/-- **The `n`-th instance of the `nameOut` matrix**: the set atom at `n`,
alongside the `n`-th instance of the body — the shape (Pr⁻) consumes. -/
theorem evInstR_inst_nameOutBody (a n : ℕ) :
    evInstR.inst (nmemAt (lvl a) (#0 : Semiterm LRA ℕ 1) (nameTerm a) ⋎ evR (body a)) n
      = nmemAt (lvl a) (num n) (numAtR a) ⋎ evInstR.inst (body a) n := by
  rw [evInstR_inst]
  have hsub : (nmemAt (lvl a) (#0 : Semiterm LRA ℕ 1) (nameTerm a) ⋎ evR (body a))/[num n]
      = (nmemAt (lvl a) (#0 : Semiterm LRA ℕ 1) (nameTerm a))/[num n] ⋎ (evR (body a))/[num n] :=
    LogicalConnective.HomClass.map_or _ _ _
  rw [hsub, subst_nmemAt_bvar0, evR_or, evR_nmemAt, evTR_num, evTR_numAtR]
  congr 1
  exact evInstR_inst_ev (body a) n

/-- **The `n`-th instance of the `nameIn` matrix**: dually, the shape (Pr)
consumes. -/
theorem evInstR_inst_nameInBody (a n : ℕ) :
    evInstR.inst (∼(evR (body a)) ⋎ memAt (lvl a) (#0 : Semiterm LRA ℕ 1) (nameTerm a)) n
      = ∼(evInstR.inst (body a) n) ⋎ memAt (lvl a) (num n) (numAtR a) := by
  rw [evInstR_inst]
  have hsub : (∼(evR (body a)) ⋎ memAt (lvl a) (#0 : Semiterm LRA ℕ 1) (nameTerm a))/[num n]
      = (∼(evR (body a)))/[num n] ⋎ (memAt (lvl a) (#0 : Semiterm LRA ℕ 1) (nameTerm a))/[num n] :=
    LogicalConnective.HomClass.map_or _ _ _
  rw [hsub, subst_memAt_bvar0, evR_or, evR_memAt, evTR_num, evTR_numAtR]
  congr 1
  have hneg : (∼(evR (body a)))/[num n] = ∼((evR (body a))/[num n]) :=
    LogicalConnective.HomClass.map_neg _ _
  rw [hneg, evR_neg]
  congr 1
  exact evInstR_inst_ev (body a) n

/-! ### Identity for an arbitrary formula

`OmegaDerivableR` has identity only for atoms (`Ramified/Calculus.lean`'s
design note explains why: D2 needs no *general* identity, only this weaker,
derived form).  This is `Omega/Identity.lean` ported to `OmegaDerivableR`: the
same induction, at the same finite height `2 · complexity`, using `and`/`or`
for the connectives and the ω-rule/`exs` for the quantifiers — the two
predicator rules never enter, since neither is principal for an identity
sequent. -/

namespace OmegaDerivableR

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals LRA} {I : InstantiationR}

/-- An instance's complexity is the body's: `InstantiationR.inst` normalises
after substituting, and both steps preserve complexity. -/
theorem complexity_instR (φ : Semiproposition LRA 1) (n : ℕ) :
    (I.inst φ n).complexity = φ.complexity :=
  I.toInstantiation.complexity_inst φ n

/-- **Identity, for members.**  A sequent containing a formula of complexity at
most `c` together with its negation is derivable, cut-free, at height `2c`. -/
theorem identity_of_mem {ρ : Gamma0Note} :
    ∀ (c : ℕ) (φ : Proposition LRA), φ.complexity ≤ c →
      ∀ {Θ : Sequent LRA}, φ ∈ Θ → ∼φ ∈ Θ →
        OmegaDerivableR A I ρ (OrdinalNotation.ofNat (2 * c) : O) Θ := by
  intro c
  induction c with
  | zero =>
      intro φ hc Θ h₁ h₂
      cases φ with
      | verum => exact of_mem_verum h₁
      | falsum => exact of_mem_verum h₂
      | rel rl v => exact of_mem_identity rl v h₁ h₂
      | nrel rl v => exact of_mem_identity rl v h₂ h₁
      | and φ ψ => simp at hc
      | or φ ψ => simp at hc
      | all φ => simp at hc
      | exs φ => simp at hc
  | succ c ih =>
      intro φ hc Θ h₁ h₂
      have hlt₁ : (OrdinalNotation.ofNat (2 * c) : O) < OrdinalNotation.ofNat (2 * c + 1) :=
        OrdinalNotation.ofNat_lt_ofNat (by omega)
      have hlt₂ : (OrdinalNotation.ofNat (2 * c + 1) : O) < OrdinalNotation.ofNat (2 * (c + 1)) :=
        OrdinalNotation.ofNat_lt_ofNat (by omega)
      cases φ with
      | verum => exact of_mem_verum h₁
      | falsum => exact of_mem_verum h₂
      | rel rl v => exact of_mem_identity rl v h₁ h₂
      | nrel rl v => exact of_mem_identity rl v h₂ h₁
      | and φ ψ =>
          simp only [Semiformula.complexity_and'] at hc
          have h₂' : (∼φ ⋎ ∼ψ) ∈ Θ := h₂
          refine drop_head (OmegaDerivableR.or hlt₂ ?_) h₂'
          refine drop_head (OmegaDerivableR.and (Γ := ∼φ :: ∼ψ :: Θ) hlt₁ hlt₁ ?_ ?_)
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h₁))
          · exact ih φ (by omega) List.mem_cons_self (by simp)
          · exact ih ψ (by omega) List.mem_cons_self (by simp)
      | or φ ψ =>
          simp only [Semiformula.complexity_or'] at hc
          have h₂' : (∼φ ⋏ ∼ψ) ∈ Θ := h₂
          refine drop_head (OmegaDerivableR.and hlt₂ hlt₂ ?_ ?_) h₂'
          · refine drop_head (OmegaDerivableR.or (Γ := ∼φ :: Θ) hlt₁ ?_)
              (List.mem_cons_of_mem _ h₁)
            exact ih φ (by omega) List.mem_cons_self (by simp)
          · refine drop_head (OmegaDerivableR.or (Γ := ∼ψ :: Θ) hlt₁ ?_)
              (List.mem_cons_of_mem _ h₁)
            exact ih ψ (by omega) (by simp) (by simp)
      | all φ =>
          simp only [Semiformula.complexity_all'] at hc
          have h₂' : (∃¹ ∼φ) ∈ Θ := h₂
          refine drop_head (OmegaDerivableR.omegaRule (Γ := Θ)
            (fun _ => OrdinalNotation.ofNat (2 * c + 1)) (fun _ => hlt₂) (fun n => ?_)) h₁
          refine drop_head (OmegaDerivableR.exs (Γ := I.inst φ n :: Θ) n hlt₁ ?_)
            (List.mem_cons_of_mem _ h₂')
          rw [InstantiationR.inst_neg]
          exact ih (I.inst φ n) (by rw [complexity_instR]; omega)
            (by simp) List.mem_cons_self
      | exs φ =>
          simp only [Semiformula.complexity_exs'] at hc
          have h₂' : (∀¹ ∼φ) ∈ Θ := h₂
          refine drop_head (OmegaDerivableR.omegaRule (Γ := Θ)
            (fun _ => OrdinalNotation.ofNat (2 * c + 1)) (fun _ => hlt₂) (fun n => ?_)) h₂'
          rw [InstantiationR.inst_neg]
          refine drop_head (OmegaDerivableR.exs (Γ := ∼I.inst φ n :: Θ) n hlt₁ ?_)
            (List.mem_cons_of_mem _ h₁)
          exact ih (I.inst φ n) (by rw [complexity_instR]; omega)
            List.mem_cons_self (by simp)

/-- **Identity.** -/
theorem identity_formula {ρ : Gamma0Note} (φ : Proposition LRA) :
    OmegaDerivableR A I ρ (OrdinalNotation.ofNat (2 * φ.complexity) : O) [φ, ∼φ] :=
  identity_of_mem φ.complexity φ le_rfl (by simp) (by simp)

end OmegaDerivableR

/-! ### The naming axioms are cut-free derivable

The height never depends on `n`: `InstantiationR.rank_nf`'s companion,
complexity preservation, makes every instance of `body a` the same complexity
as `body a` itself, so the identity sequent underneath the (Pr)/(Pr⁻)
inference sits at a single finite height, uniform in `n`, and the outer
ω-rule needs no growing family. -/

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- **Every `nameOut` axiom is cut-free derivable.** -/
theorem nameOut_derivable {a : ℕ} (hg : Good a) (hp : ParamFree a) :
    ∃ β : O, OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb (Semiformula.univCl (nameOut a)) : Proposition LRA)] := by
  have hfv : (nameOut a).freeVariables = ∅ := freeVariables_nameOut hp
  rw [emb_univCl_of_freeVariables_eq_empty hfv, ev_nameOut]
  set c : ℕ := (body a).complexity with hc
  refine ⟨OrdinalNotation.ofNat (2 * c + 3), ?_⟩
  refine OmegaDerivableR.omegaRule (Γ := ([] : Sequent LRA))
    (fun _ => OrdinalNotation.ofNat (2 * c + 2))
    (fun _ => OrdinalNotation.ofNat_lt_ofNat (by omega)) (fun n => ?_)
  rw [evInstR_inst_nameOutBody]
  set ψ : Proposition LRA := evInstR.inst (body a) n with hψdef
  have hψc : ψ.complexity = c := by
    rw [hψdef, hc]; exact OmegaDerivableR.complexity_instR (body a) n
  refine OmegaDerivableR.or (α := OrdinalNotation.ofNat (2 * c + 2))
    (β := OrdinalNotation.ofNat (2 * c + 1)) (Γ := ([] : Sequent LRA))
    (OrdinalNotation.ofNat_lt_ofNat (by omega)) ?_
  refine OmegaDerivableR.npr (α := OrdinalNotation.ofNat (2 * c + 1))
    (β := OrdinalNotation.ofNat (2 * c)) hg (OrdinalNotation.ofNat_lt_ofNat (by omega)) ?_
  have hident : OmegaDerivableR trueArithLitsR evInstR 0
      (OrdinalNotation.ofNat (2 * c) : O) [ψ, ∼ψ] := by
    rw [← hψc]; exact OmegaDerivableR.identity_formula ψ
  exact OmegaDerivableR.contraction (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
    hident

/-- **Every `nameIn` axiom is cut-free derivable.** -/
theorem nameIn_derivable {a : ℕ} (hg : Good a) (hp : ParamFree a) :
    ∃ β : O, OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb (Semiformula.univCl (nameIn a)) : Proposition LRA)] := by
  have hfv : (nameIn a).freeVariables = ∅ := freeVariables_nameIn hp
  rw [emb_univCl_of_freeVariables_eq_empty hfv, ev_nameIn]
  set c : ℕ := (body a).complexity with hc
  refine ⟨OrdinalNotation.ofNat (2 * c + 3), ?_⟩
  refine OmegaDerivableR.omegaRule (Γ := ([] : Sequent LRA))
    (fun _ => OrdinalNotation.ofNat (2 * c + 2))
    (fun _ => OrdinalNotation.ofNat_lt_ofNat (by omega)) (fun n => ?_)
  rw [evInstR_inst_nameInBody]
  set ψ : Proposition LRA := evInstR.inst (body a) n with hψdef
  have hψc : ψ.complexity = c := by
    rw [hψdef, hc]; exact OmegaDerivableR.complexity_instR (body a) n
  refine OmegaDerivableR.or (α := OrdinalNotation.ofNat (2 * c + 2))
    (β := OrdinalNotation.ofNat (2 * c + 1)) (Γ := ([] : Sequent LRA))
    (OrdinalNotation.ofNat_lt_ofNat (by omega)) ?_
  refine OmegaDerivableR.contraction
    (Δ := [memAt (lvl a) (num n) (numAtR a), ∼ψ])
    (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) ?_
  refine OmegaDerivableR.pr (α := OrdinalNotation.ofNat (2 * c + 1))
    (β := OrdinalNotation.ofNat (2 * c)) hg (OrdinalNotation.ofNat_lt_ofNat (by omega)) ?_
  have hident : OmegaDerivableR trueArithLitsR evInstR 0
      (OrdinalNotation.ofNat (2 * c) : O) [ψ, ∼ψ] := by
    rw [← hψc]; exact OmegaDerivableR.identity_formula ψ
  exact hident

/-- **Every axiom of the naming schema is cut-free derivable.** -/
theorem naming_axiom_derivable {Λ : Set Lv} {σ : Sentence LRA} (h : σ ∈ NamingAxioms Λ) :
    ∃ β : O, OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb σ : Proposition LRA)] := by
  obtain ⟨a, hg, hp, -, rfl | rfl⟩ := h
  · exact nameOut_derivable hg hp
  · exact nameIn_derivable hg hp

/-- **A naming axiom at a level below `ν` has rank below `ω^ν`.**  The half of
the naming schema `Rank.lean`'s `rank_lt_omegaPow_of_level` was built for:
`lvlOf_nameOut`/`lvlOf_nameIn` locate the level of the axiom at `lvl a`, and
`evR` moves neither the level nor the rank. -/
theorem rank_evR_emb_naming_lt {ν : Lv} {σ : Sentence LRA} (h : σ ∈ NamingAxioms {μ | μ < ν}) :
    rank (evR (Rewriting.emb σ : Proposition LRA)) < omegaPowLv ν := by
  obtain ⟨a, hg, hp, hν, rfl | rfl⟩ := h
  · rw [emb_univCl_of_freeVariables_eq_empty (freeVariables_nameOut hp), rank_evR]
    exact rank_lt_omegaPow_of_level (by rw [lvlOf_nameOut hg]; exact hν)
  · rw [emb_univCl_of_freeVariables_eq_empty (freeVariables_nameIn hp), rank_evR]
    exact rank_lt_omegaPow_of_level (by rw [lvlOf_nameIn hg]; exact hν)

end Ramified

end OrdinalAnalysis
