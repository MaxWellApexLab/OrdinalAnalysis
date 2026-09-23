/-
  Every naming axiom of `RA_∞` is cut-free derivable, and its rank is below the
  level it names.

  `Theory.lean` supplies two axioms per level `μ > 0` and formula `A` of shape
  `μ`, uniform in the code:

      nameOutP μ A :≡ ∀c ∀p ∀s (G(c, p, s) → ∀x (x ∈̇_μ c → A(x, p)))
      nameInP  μ A :≡ ∀c ∀p ∀s (G(c, p, s) → ∀x (A(x, p) → x ∈̇_μ c))

  with `G` the arithmetical guard `c = ⟨μ, s, ⌜A⌝, p⟩ ∧ A.complexity + stage p < s`.
  This file shows that `RA_∞ ⊢^0_β evR (emb (univCl (nameOutP μ A)))` for a
  finite `β`, and likewise for `nameInP μ A`, and that the rank of the
  evaluated, embedded axiom is below `ω · ν` for `μ < ν`.  Together with
  `Ramified/CutAxioms.lean`'s `cut_axioms_of`, this is what lets the naming
  schema of `RA Λ` be cut away.

  ## The route

  **The axioms are closed.**  Every free variable of `A` is sent to the bound
  parameter, and the guard is a transported arithmetical semisentence, so
  `univCl` adds nothing (`emb_univCl_nameOutP`).

  **Three ω-rules over `c`, `p`, `s`** (`AxiomsLogic.allClosureR_derivable`),
  after which the numbers are fixed and the guard is a closed arithmetical
  formula, decided in `ℕ` (`eval_guardR_subst`):

  * if it is false, its negation is a true closed arithmetical formula, derived
    by ω-completeness (`AxiomsLogic.omega_completeR`);
  * if it is true, `c = ⟨μ, s, ⌜A⌝, p⟩` is a `Good` code with body
    `A(·, p)`, and one more ω-rule over the subject, one (Pr⁻) (for `nameOutP`)
    or (Pr) (for `nameInP`) inference and one identity sequent derive the
    instance at a height uniform in the subject.

  Every height is a fixed finite number depending only on `A`: the guard's
  complexity for the first case, twice the complexity of `A` plus a constant for
  the second.

  **The rank bound.**  `lvlOf (nameOutP μ A) = lvlOf (nameInP μ A) = μ`
  (`Theory.lean`), `evR` preserves the level, and `Rank.lean`'s
  `rank_lt_block_of_level` turns "level below `ν`" into "rank below `ω · ν`".
-/
import OrdinalAnalysis.Ramified.Theory
import OrdinalAnalysis.Ramified.AxiomsLogic

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Derivation LO.FirstOrder.Arithmetic

/-! ### Closing a variable-free proposition is the identity -/

/-- **Closing a variable-free proposition and embedding it back gives the
proposition itself.** -/
theorem emb_univCl_of_freeVariables_eq_empty {φ : Proposition LRA} (h : φ.freeVariables = ∅) :
    (Rewriting.emb (Semiformula.univCl φ) : Proposition LRA) = φ := by
  rw [Semiformula.coe_univCl_eq_univCl', Semiformula.univCl'_eq_self_of φ h]

/-! ### Free variables -/

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

/-- A rewriting that sends every variable to a variable-free term yields a
variable-free formula. -/
theorem freeVariables_rew_eq_empty_of {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂)
    (φ : Semiformula LRA ℕ n₁) (hb : ∀ i : Fin n₁, (ω #i).freeVariables = ∅)
    (hf : ∀ x : ℕ, (ω &x).freeVariables = ∅) : (ω ▹ φ).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := ω) (φ := φ) (x := x) hx with ⟨i, hi⟩ | ⟨z, -, hz⟩
  · rw [Semiterm.FVar?, hb i] at hi
    exact Finset.notMem_empty x hi
  · rw [Semiterm.FVar?, hf z] at hz
    exact Finset.notMem_empty x hz

theorem freeVariables_guardR (μ : Lv) (A : Semiformula LRA ℕ 1) :
    (guardR μ A).freeVariables = ∅ := by
  simp [guardR]

theorem freeVariables_instA (A : Semiformula LRA ℕ 1) : (instA A).freeVariables = ∅ := by
  refine freeVariables_rew_eq_empty_of _ A (fun i => ?_) (fun x => ?_)
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  · rfl

theorem freeVariables_nameOutP (μ : Lv) (A : Semiformula LRA ℕ 1) :
    (nameOutP μ A).freeVariables = ∅ := by
  simp [nameOutP, nameOutMat, freeVariables_guardR, freeVariables_instA, freeVariables_nmemAt]

theorem freeVariables_nameInP (μ : Lv) (A : Semiformula LRA ℕ 1) :
    (nameInP μ A).freeVariables = ∅ := by
  simp [nameInP, nameInMat, freeVariables_guardR, freeVariables_instA, freeVariables_memAt]

theorem emb_univCl_nameOutP (μ : Lv) (A : Semiformula LRA ℕ 1) :
    (Rewriting.emb (Semiformula.univCl (nameOutP μ A)) : Proposition LRA) = nameOutP μ A :=
  emb_univCl_of_freeVariables_eq_empty (freeVariables_nameOutP μ A)

theorem emb_univCl_nameInP (μ : Lv) (A : Semiformula LRA ℕ 1) :
    (Rewriting.emb (Semiformula.univCl (nameInP μ A)) : Proposition LRA) = nameInP μ A :=
  emb_univCl_of_freeVariables_eq_empty (freeVariables_nameInP μ A)

/-! ### Rewriting a set atom

A term carrying `Sum.inr (RARel.mem μ) : LRA.Rel 2` is not type-correct at
implicit transparency, so `rw` and `simp` do not enter `memAt`; the two
equations are `Semiformula.rew_rel2`/`rew_nrel2` followed by `congrArg`. -/

theorem rew_memAt {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (μ : Lv) (t s : Semiterm LRA ℕ n₁) :
    ω ▹ memAt μ t s = memAt μ (ω t) (ω s) :=
  Semiformula.rew_rel2 ω (r := (Sum.inr (RARel.mem μ) : LRA.Rel 2)) (t₁ := t) (t₂ := s)

theorem rew_nmemAt {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (μ : Lv) (t s : Semiterm LRA ℕ n₁) :
    ω ▹ nmemAt μ t s = nmemAt μ (ω t) (ω s) :=
  Semiformula.rew_nrel2 ω (r := (Sum.inr (RARel.mem μ) : LRA.Rel 2)) (t₁ := t) (t₂ := s)

/-! ### The guard at numerals -/

/-- The numeral of `n` has value `n` in every standard structure, whatever the
environment. -/
theorem val_numAtR_stdLRA {n : ℕ} (e : Fin n → ℕ) (f : ℕ → ℕ) (m : ℕ) :
    Semiterm.val (s := stdLRA) e f (numAtR m : Semiterm LRA ℕ n) = m := by
  rw [stdLRA_eq_raStd, val_groundR raStruc (groundR_numAtR m) e f, evTermR_numAtR]

/-- **The guard at numerals is decided in `ℕ`.** -/
theorem eval_guardR_subst (μ : Lv) (A : Semiformula LRA ℕ 1) (w : Fin 3 → ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := stdLRA) ![] f
        (guardR μ A ⇜ fun i => (numAtR (w i) : SyntacticTerm LRA)) ↔
      w 0 = mkCode μ (w 2) (Encodable.encode A) (w 1) ∧ A.complexity + stage (w 1) < w 2 := by
  rw [← eval_guardDef_nat, Semiformula.eval_substs]
  have hv : (Semiterm.val (s := stdLRA) ![] f ∘ fun i => (numAtR (w i) : SyntacticTerm LRA)) = w :=
    funext fun i => val_numAtR_stdLRA ![] f (w i)
  rw [hv, guardR, stdLRA_eq_raStd, eval_lMap_toLRA, Semiformula.eval_emb, guardSS,
    Semiformula.eval_rew]
  apply iff_of_eq
  congr 2
  funext i
  fin_cases i <;> simp [Rew.subst_bvar]

/-- `R`-freeness of the guard. -/
theorem rFree_guardR (μ : Lv) (A : Semiformula LRA ℕ 1) : RFree (guardR μ A) :=
  rFree_lMap_toLRA _

/-- **A false guard is refuted cut-free**, by ω-completeness, at the height of
its complexity. -/
theorem guardR_refutable (μ : Lv) (A : Semiformula LRA ℕ 1) (w : Fin 3 → ℕ)
    (hg : ¬(w 0 = mkCode μ (w 2) (Encodable.encode A) (w 1) ∧
      A.complexity + stage (w 1) < w 2)) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
      (OrdinalNotation.ofNat (guardR μ A).complexity)
      [evR (∼(guardR μ A ⇜ fun i => (numAtR (w i) : SyntacticTerm LRA)))] := by
  have h := omega_completeR (∼(guardR μ A ⇜ fun i => (numAtR (w i) : SyntacticTerm LRA)))
    ((rFree_neg _).mpr (rFree_rew _ (rFree_guardR μ A)))
    (by
      rw [Semiformula.freeVariables_not]
      exact freeVariables_rewR_eq_empty _ (freeVariables_guardR μ A)
        (fun i => freeVariables_of_groundR (groundR_numAtR _)))
    (by
      simp only [LogicalConnective.HomClass.map_neg]
      exact fun ht => hg ((eval_guardR_subst μ A w _).mp ht))
  have hc : (∼(guardR μ A ⇜ fun i => (numAtR (w i) : SyntacticTerm LRA))).complexity
      = (guardR μ A).complexity := by
    rw [Semiformula.complexity_neg]
    exact Semiformula.complexity_rew _ _
  rw [hgtR, hc] at h
  exact h

/-! ### The instance of the body at a code -/

/-- Substituting the subject and the three code numbers into `A(x, p)` is the
`n`-th instance of the body of a code with parameter `w 1`. -/
theorem subst_instA (A : Semiformula LRA ℕ 1) (w : Fin 3 → ℕ) (n : ℕ) :
    instA A ⇜ ((num n : SyntacticTerm LRA) :> fun i => (numAtR (w i) : SyntacticTerm LRA))
      = (instParam (w 1) ▹ A)/[(num n : SyntacticTerm LRA)] := by
  have hrew : (Rew.subst ((num n : SyntacticTerm LRA) :>
        fun i => (numAtR (w i) : SyntacticTerm LRA))).comp
        (Rew.bind ![(#0 : Semiterm LRA ℕ 4)] (fun _ => #2))
      = (Rew.subst ![(num n : SyntacticTerm LRA)]).comp (instParam (w 1)) := by
    ext x
    · have hx : x = 0 := Subsingleton.elim x 0
      subst hx
      simp [Rew.comp_app, instParam]
    · simp [Rew.comp_app, instParam, numAtR]
  show Rew.subst _ ▹ (Rew.bind _ _ ▹ A) = Rew.subst _ ▹ (instParam (w 1) ▹ A)
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, hrew]

/-- The subject-instance of the `nameOutP` matrix body, after evaluation. -/
theorem ev_inst_nameOutBody (μ : Lv) (A : Semiformula LRA ℕ 1) (w : Fin 3 → ℕ) (n : ℕ) :
    evInstR.inst (evR ((Rew.subst fun i => (numAtR (w i) : SyntacticTerm LRA)).q ▹
        (nmemAt μ (#0 : Semiterm LRA ℕ 4) #1 ⋎ instA A))) n
      = nmemAt μ (num n) (numAtR (w 0)) ⋎ evR ((instParam (w 1) ▹ A)/[(num n : SyntacticTerm LRA)]) := by
  rw [evInstR_inst_ev, subst_q_substR]
  have hsplit : ((nmemAt μ (#0 : Semiterm LRA ℕ 4) #1 ⋎ instA A) ⇜
        ((num n : SyntacticTerm LRA) :> fun i => (numAtR (w i) : SyntacticTerm LRA)))
      = nmemAt μ (num n) (numAtR (w 0)) ⋎ (instParam (w 1) ▹ A)/[(num n : SyntacticTerm LRA)] := by
    rw [← subst_instA A w n]
    show Rew.subst _ ▹ (nmemAt μ (#0 : Semiterm LRA ℕ 4) #1 ⋎ instA A) = _
    rw [LogicalConnective.HomClass.map_or, rew_nmemAt]
    rfl
  rw [hsplit, evR_or, evR_nmemAt, evTR_num, evTR_numAtR]

/-- The subject-instance of the `nameInP` matrix body, after evaluation. -/
theorem ev_inst_nameInBody (μ : Lv) (A : Semiformula LRA ℕ 1) (w : Fin 3 → ℕ) (n : ℕ) :
    evInstR.inst (evR ((Rew.subst fun i => (numAtR (w i) : SyntacticTerm LRA)).q ▹
        (∼(instA A) ⋎ memAt μ (#0 : Semiterm LRA ℕ 4) #1))) n
      = ∼evR ((instParam (w 1) ▹ A)/[(num n : SyntacticTerm LRA)]) ⋎ memAt μ (num n) (numAtR (w 0)) := by
  rw [evInstR_inst_ev, subst_q_substR]
  have hsplit : ((∼(instA A) ⋎ memAt μ (#0 : Semiterm LRA ℕ 4) #1) ⇜
        ((num n : SyntacticTerm LRA) :> fun i => (numAtR (w i) : SyntacticTerm LRA)))
      = ∼((instParam (w 1) ▹ A)/[(num n : SyntacticTerm LRA)]) ⋎ memAt μ (num n) (numAtR (w 0)) := by
    rw [← subst_instA A w n]
    show Rew.subst _ ▹ (∼(instA A) ⋎ memAt μ (#0 : Semiterm LRA ℕ 4) #1) = _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, rew_memAt]
    rfl
  rw [hsplit, evR_or, evR_neg, evR_memAt, evTR_num, evTR_numAtR]

/-! ### Identity for an arbitrary formula

`OmegaDerivableR` has identity only for atoms (`Ramified/Calculus.lean`'s
header explains why: D2 needs no *general* identity, only this weaker,
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

The three outer quantifiers are peeled at once by `allClosureR_derivable`; each
numeral instance is derived at the height `g + 2c + 4`, with `g` the complexity
of the guard and `c` that of `A` — uniform in the three numbers. -/

/-- **One numeral instance of `nameOutP`**, at a height depending only on `A`. -/
theorem nameOutMat_inst_derivable {μ : Lv} {A : Semiformula LRA ℕ 1} (h0 : 0 < μ)
    (hA : Shape μ A) (w : Fin 3 → ℕ) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
      (OrdinalNotation.ofNat ((guardR μ A).complexity + 2 * A.complexity + 4))
      [evR (nameOutMat μ A ⇜ fun i => (numAtR (w i) : SyntacticTerm LRA))] := by
  set v : Fin 3 → SyntacticTerm LRA := fun i => numAtR (w i) with hv
  set g : ℕ := (guardR μ A).complexity with hgdef
  set c : ℕ := A.complexity with hcdef
  have hsplit : (nameOutMat μ A ⇜ v) = ∼(guardR μ A ⇜ v) ⋎
      (∀¹ ((Rew.subst v).q ▹ (nmemAt μ (#0 : Semiterm LRA ℕ 4) #1 ⋎ instA A))) := by
    show Rew.subst v ▹ (∼(guardR μ A) ⋎ (∀¹ _)) = _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, Rewriting.app_all]
  rw [hsplit, evR_or, evR_all]
  refine OmegaDerivableR.or (β := OrdinalNotation.ofNat (g + 2 * c + 3))
    (OrdinalNotation.ofNat_lt_ofNat (by omega)) ?_
  by_cases hg : w 0 = mkCode μ (w 2) (Encodable.encode A) (w 1) ∧ c + stage (w 1) < w 2
  · obtain ⟨hw0, hst⟩ := hg
    have hgood : Good (w 0) := by rw [hw0]; exact good_mkCode h0 hA hst
    have hbody : body (w 0) = instParam (w 1) ▹ A := by rw [hw0, body_mkCode]
    have hlvl : lvl (w 0) = μ := by rw [hw0, lvl_mkCode]
    refine OmegaDerivableR.contraction
      (Δ := [∀¹ evR ((Rew.subst v).q ▹ (nmemAt μ (#0 : Semiterm LRA ℕ 4) #1 ⋎ instA A)),
        evR (∼(guardR μ A ⇜ v))])
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
    refine OmegaDerivableR.mono_ord ?_ (ofNat_le_ofNat (show 2 * c + 3 ≤ g + 2 * c + 3 by omega))
    refine OmegaDerivableR.omegaRule (fun _ => OrdinalNotation.ofNat (2 * c + 2))
      (fun _ => OrdinalNotation.ofNat_lt_ofNat (by omega)) (fun n => ?_)
    rw [hv, ev_inst_nameOutBody]
    set ψ : Proposition LRA := evInstR.inst (body (w 0)) n with hψ
    have hψe : evR ((instParam (w 1) ▹ A)/[(num n : SyntacticTerm LRA)]) = ψ := by
      rw [hψ, evInstR_inst, hbody]
    have hψc : ψ.complexity = c := by
      rw [hψ, OmegaDerivableR.complexity_instR, hbody, Semiformula.complexity_rew]
    rw [hψe]
    refine OmegaDerivableR.or (β := OrdinalNotation.ofNat (2 * c + 1))
      (OrdinalNotation.ofNat_lt_ofNat (by omega)) ?_
    have hid : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
        (OrdinalNotation.ofNat (2 * c)) [ψ, ∼ψ] := by
      rw [← hψc]; exact OmegaDerivableR.identity_formula ψ
    have hnpr := OmegaDerivableR.npr (A := trueArithLitsR) (I := evInstR) (ρ := 0)
      (α := (OrdinalNotation.ofNat (2 * c + 1) : Gamma0Note))
      (β := OrdinalNotation.ofNat (2 * c)) (a := w 0) (n := n)
      (Γ := ψ :: [evR (∼(guardR μ A ⇜ fun i => (numAtR (w i) : SyntacticTerm LRA)))]) hgood
      (OrdinalNotation.ofNat_lt_ofNat (by omega))
      (OmegaDerivableR.contraction
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) hid)
    subst hlvl
    exact hnpr
  · exact OmegaDerivableR.contraction
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
      ((guardR_refutable μ A w hg).mono_ord (ofNat_le_ofNat (by omega)))

/-- **One numeral instance of `nameInP`**, at a height depending only on `A`. -/
theorem nameInMat_inst_derivable {μ : Lv} {A : Semiformula LRA ℕ 1} (h0 : 0 < μ)
    (hA : Shape μ A) (w : Fin 3 → ℕ) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
      (OrdinalNotation.ofNat ((guardR μ A).complexity + 2 * A.complexity + 4))
      [evR (nameInMat μ A ⇜ fun i => (numAtR (w i) : SyntacticTerm LRA))] := by
  set v : Fin 3 → SyntacticTerm LRA := fun i => numAtR (w i) with hv
  set g : ℕ := (guardR μ A).complexity with hgdef
  set c : ℕ := A.complexity with hcdef
  have hsplit : (nameInMat μ A ⇜ v) = ∼(guardR μ A ⇜ v) ⋎
      (∀¹ ((Rew.subst v).q ▹ (∼(instA A) ⋎ memAt μ (#0 : Semiterm LRA ℕ 4) #1))) := by
    show Rew.subst v ▹ (∼(guardR μ A) ⋎ (∀¹ _)) = _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, Rewriting.app_all]
  rw [hsplit, evR_or, evR_all]
  refine OmegaDerivableR.or (β := OrdinalNotation.ofNat (g + 2 * c + 3))
    (OrdinalNotation.ofNat_lt_ofNat (by omega)) ?_
  by_cases hg : w 0 = mkCode μ (w 2) (Encodable.encode A) (w 1) ∧ c + stage (w 1) < w 2
  · obtain ⟨hw0, hst⟩ := hg
    have hgood : Good (w 0) := by rw [hw0]; exact good_mkCode h0 hA hst
    have hbody : body (w 0) = instParam (w 1) ▹ A := by rw [hw0, body_mkCode]
    have hlvl : lvl (w 0) = μ := by rw [hw0, lvl_mkCode]
    refine OmegaDerivableR.contraction
      (Δ := [∀¹ evR ((Rew.subst v).q ▹ (∼(instA A) ⋎ memAt μ (#0 : Semiterm LRA ℕ 4) #1)),
        evR (∼(guardR μ A ⇜ v))])
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
    refine OmegaDerivableR.mono_ord ?_ (ofNat_le_ofNat (show 2 * c + 3 ≤ g + 2 * c + 3 by omega))
    refine OmegaDerivableR.omegaRule (fun _ => OrdinalNotation.ofNat (2 * c + 2))
      (fun _ => OrdinalNotation.ofNat_lt_ofNat (by omega)) (fun n => ?_)
    rw [hv, ev_inst_nameInBody]
    set ψ : Proposition LRA := evInstR.inst (body (w 0)) n with hψ
    have hψe : evR ((instParam (w 1) ▹ A)/[(num n : SyntacticTerm LRA)]) = ψ := by
      rw [hψ, evInstR_inst, hbody]
    have hψc : ψ.complexity = c := by
      rw [hψ, OmegaDerivableR.complexity_instR, hbody, Semiformula.complexity_rew]
    rw [hψe]
    refine OmegaDerivableR.or (β := OrdinalNotation.ofNat (2 * c + 1))
      (OrdinalNotation.ofNat_lt_ofNat (by omega)) ?_
    have hid : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
        (OrdinalNotation.ofNat (2 * c)) [ψ, ∼ψ] := by
      rw [← hψc]; exact OmegaDerivableR.identity_formula ψ
    have hpr := OmegaDerivableR.pr (A := trueArithLitsR) (I := evInstR) (ρ := 0)
      (α := (OrdinalNotation.ofNat (2 * c + 1) : Gamma0Note))
      (β := OrdinalNotation.ofNat (2 * c)) (a := w 0) (n := n)
      (Γ := ∼ψ :: [evR (∼(guardR μ A ⇜ fun i => (numAtR (w i) : SyntacticTerm LRA)))]) hgood
      (OrdinalNotation.ofNat_lt_ofNat (by omega))
      (OmegaDerivableR.contraction
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) hid)
    subst hlvl
    exact OmegaDerivableR.contraction
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) hpr
  · exact OmegaDerivableR.contraction
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
      ((guardR_refutable μ A w hg).mono_ord (ofNat_le_ofNat (by omega)))

/-- **Every `nameOutP` axiom is cut-free derivable**, at a finite height. -/
theorem nameOutP_derivable {μ : Lv} {A : Semiformula LRA ℕ 1} (h0 : 0 < μ) (hA : Shape μ A) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
      (OrdinalNotation.nadd
        (OrdinalNotation.ofNat ((guardR μ A).complexity + 2 * A.complexity + 4))
        (OrdinalNotation.ofNat 3))
      [evR (Rewriting.emb (Semiformula.univCl (nameOutP μ A)) : Proposition LRA)] := by
  rw [emb_univCl_nameOutP, nameOutP]
  exact allClosureR_derivable (nameOutMat μ A) (nameOutMat_inst_derivable h0 hA)

/-- **Every `nameInP` axiom is cut-free derivable**, at a finite height. -/
theorem nameInP_derivable {μ : Lv} {A : Semiformula LRA ℕ 1} (h0 : 0 < μ) (hA : Shape μ A) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
      (OrdinalNotation.nadd
        (OrdinalNotation.ofNat ((guardR μ A).complexity + 2 * A.complexity + 4))
        (OrdinalNotation.ofNat 3))
      [evR (Rewriting.emb (Semiformula.univCl (nameInP μ A)) : Proposition LRA)] := by
  rw [emb_univCl_nameInP, nameInP]
  exact allClosureR_derivable (nameInMat μ A) (nameInMat_inst_derivable h0 hA)

/-- **Every axiom of the naming schema is cut-free derivable.** -/
theorem naming_axiom_derivable {Λ : Set Lv} {σ : Sentence LRA} (h : σ ∈ NamingAxioms Λ) :
    ∃ β : Gamma0Note, OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb σ : Proposition LRA)] := by
  obtain ⟨μ, A, -, h0, hA, rfl | rfl⟩ := h
  · exact ⟨_, nameOutP_derivable h0 hA⟩
  · exact ⟨_, nameInP_derivable h0 hA⟩

/-- **A naming axiom at a level below `ν` has rank below `ω · ν`.**
`lvlOf_nameOutP`/`lvlOf_nameInP` locate the level of the axiom at `μ`, and `evR`
moves neither the level nor the rank. -/
theorem rank_evR_emb_naming_lt {ν : Lv} {σ : Sentence LRA} (h : σ ∈ NamingAxioms {μ | μ < ν}) :
    rank (evR (Rewriting.emb σ : Proposition LRA)) < omegaMul ν := by
  obtain ⟨μ, A, hν, -, hA, rfl | rfl⟩ := h
  · rw [emb_univCl_nameOutP, rank_evR]
    exact rank_lt_block_of_level (by rw [lvlOf_nameOutP hA]; exact hν)
  · rw [emb_univCl_nameInP, rank_evR]
    exact rank_lt_block_of_level (by rw [lvlOf_nameInP hA]; exact hν)

end Ramified

end OrdinalAnalysis
