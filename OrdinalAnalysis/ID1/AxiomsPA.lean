/-
  The induction axioms of `PA` over `LXI` in the infinitary calculus of `ID₁`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, proof of Theorem 6.5: "the axioms of `PA ⊆ ID₁`,
  including induction for the extended language `L_ID`, are treated as in the proof of
  Theorem 3.7 from the first lecture".

  **The argument** (Theorem 3.7 of the first lecture, for the ω-rule).  For the body `ψ` of
  an induction axiom, with its free variables already replaced by numerals, the chain

      ¬ψ(0), ∃x (ψ(x) ∧ ¬ψ(x + 1)), ψ(n̄)          at height ω · rk ψ ⊕ 2n

  is built by induction on `n`: the base is Lemma 6.1, and the step is clause (W) on the
  existential at the witness `n̄`, with the conjunction `ψ(n̄) ∧ ¬ψ(n̄ + 1)` from the chain
  for `n` and from Lemma 6.1 for `ψ(n+1)`.  The instance `ψ(n̄ + 1)` of the induction step and
  the numeral `ψ((n+1)‾)` of the ω-rule differ in a closed term of the same value; Freund's
  remark on the replacement of closed terms (`IDerivable.replace_head`) reconciles them.  The
  ω-rule then gives `∀x ψ(x)` at height `ω · rk ψ ⊕ ω`, two disjunction steps the axiom, and
  the universal closure is peeled by the ω-rule once for every free variable.

  Contents.

    `embT_numeral`, `sucX`, `sucI`, `embT_sucX`, `val_subst_sucI`
    `succIndI`, `numSubst_embK_succInd`   the embedded axiom under a numeral assignment
    `chain`, `succIndI_derivable`
    `omegaMul_nadd`                       `ω · (α ⊕ β) = ω · α ⊕ ω · β`
    `induction_axiom`                     **every induction axiom**
-/
import OrdinalAnalysis.ID1.AxiomsLogic

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaNote

/-- **`ω · (α ⊕ β) = ω · α ⊕ ω · β`**: both exponent lists are the non-increasing arrangement
of the same entries `1 + α_i`, `1 + β_j`. -/
theorem omegaMul_nadd (a b : ThetaNote) :
    omegaMul (ThetaNote.nadd a b) = ThetaNote.nadd (omegaMul a) (omegaMul b) :=
  ext_entries (by
    have h1 := sorted_entries (omegaMul (ThetaNote.nadd a b))
    have h2 := sorted_entries (ThetaNote.nadd (omegaMul a) (omegaMul b))
    rw [entries_omegaMul, entries_nadd] at h1
    rw [entries_nadd, entries_omegaMul, entries_omegaMul] at h2
    rw [entries_omegaMul, entries_nadd, entries_nadd, entries_omegaMul, entries_omegaMul]
    refine ThetaTerm.eq_of_perm_of_sortedDesc h1 h2 ?_
    refine ((ThetaTerm.mergeL_perm _ _).map _).trans ?_
    rw [List.map_append]
    exact (ThetaTerm.mergeL_perm _ _).symm)

end ThetaNote

namespace InductiveDef

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting
open LO.FirstOrder.Arithmetic

/-! ### Terms under the embedding -/

section Terms

variable {ξ : Type*} {n : ℕ}

private lemma embT_numeral_zero :
    embT ((0 : ℕ) : Semiterm LXI ξ n) = ((0 : ℕ) : Semiterm LIinf ξ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, stageHom, stageFunc]
  rfl

private lemma embT_numeral_one :
    embT ((1 : ℕ) : Semiterm LXI ξ n) = ((1 : ℕ) : Semiterm LIinf ξ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, stageHom, stageFunc]
  rfl

theorem embT_add (v : Fin 2 → Semiterm LXI ξ n) :
    embT (Semiterm.Operator.Add.add.operator v) =
      Semiterm.Operator.Add.add.operator (embT ∘ v) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, stageHom, stageFunc]
  refine congrArg (Semiterm.func (Language.Add.add : LIinf.Func 2)) ?_
  funext i
  rfl

private lemma numeralX_succ_succ (L : Language) [L.Zero] [L.One] [L.Add] (k : ℕ) :
    ((k + 1 + 1 : ℕ) : Semiterm L ξ n) =
      Semiterm.Operator.Add.add.operator
        ![((k + 1 : ℕ) : Semiterm L ξ n), ((1 : ℕ) : Semiterm L ξ n)] := by
  have h : k + 1 ≠ 0 := Nat.succ_ne_zero k
  simp only [Semiterm.numeral, Semiterm.Operator.const,
    Semiterm.Operator.numeral_succ h, Semiterm.Operator.operator_comp]
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- The embedding fixes the numerals. -/
theorem embT_numeral (k : ℕ) :
    embT ((k : ℕ) : Semiterm LXI ξ n) = ((k : ℕ) : Semiterm LIinf ξ n) := by
  induction k with
  | zero => exact embT_numeral_zero
  | succ k ih =>
    cases k with
    | zero => exact embT_numeral_one
    | succ k =>
      rw [numeralX_succ_succ LXI k, numeralX_succ_succ LIinf k, embT_add]
      congr 1
      funext i
      match i with
      | ⟨0, _⟩ => exact ih
      | ⟨1, _⟩ => exact embT_numeral_one

end Terms

/-- The successor term `#0 + 1` of `LXI`. -/
def sucX : Semiterm LXI ℕ 1 := ‘(#0 + 1)’

/-- The successor term `#0 + 1` of `LIinf`. -/
def sucI : Semiterm LIinf ℕ 1 := ‘(#0 + 1)’

theorem embT_sucX : embT sucX = sucI := by
  rw [sucX, sucI]
  show embT (Semiterm.Operator.Add.add.operator ![#0, ((1 : ℕ) : Semiterm LXI ℕ 1)]) = _
  rw [embT_add]
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => exact embT_numeral 1

/-- `+` in operator form is `+` in function form. -/
theorem add_operator_eq_func {n : ℕ} (a b : Semiterm LIinf ℕ n) :
    Semiterm.Operator.Add.add.operator ![a, b]
      = Semiterm.func (Language.Add.add : LIinf.Func 2) ![a, b] := by
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func]
  exact congrArg (Semiterm.func (Language.Add.add : LIinf.Func 2))
    (by funext i; match i with
        | ⟨0, _⟩ => simp
        | ⟨1, _⟩ => simp)

theorem subst_sucI (t : SyntacticTerm LIinf) :
    Rew.subst ![t] sucI =
      Semiterm.func (Language.Add.add : LIinf.Func 2) ![t, ((1 : ℕ) : SyntacticTerm LIinf)] := by
  rw [← add_operator_eq_func]
  simp [sucI]

/-- The successor term with a closed term substituted has the successor value. -/
theorem val_subst_sucI (t : SyntacticTerm LIinf) (e : Fin 0 → ℕ) (ε : ℕ → ℕ) :
    Semiterm.val (s := stdInf) e ε (Rew.subst ![t] sucI) =
      Semiterm.val (s := stdInf) e ε t + 1 := by
  rw [subst_sucI, Semiterm.val_func]
  change Semiterm.val (s := stdInf) e ε t +
    Semiterm.val (s := stdInf) e ε ((1 : ℕ) : SyntacticTerm LIinf) = _
  rw [val_numeral_stdInf]

theorem freeVariables_subst_sucI {t : SyntacticTerm LIinf} (ht : t.freeVariables = ∅) :
    (Rew.subst ![t] sucI).freeVariables = ∅ := by
  rw [subst_sucI, Semiterm.freeVariables_func]
  ext x
  simp only [Finset.notMem_empty, iff_false, Finset.mem_biUnion, Finset.mem_univ, true_and,
    not_exists]
  intro i hx
  match i with
  | ⟨0, h⟩ =>
    have h0 : (![t, ((1 : ℕ) : SyntacticTerm LIinf)] : Fin 2 → SyntacticTerm LIinf) ⟨0, h⟩ = t :=
      rfl
    rw [h0, ht] at hx
    exact Finset.notMem_empty x hx
  | ⟨1, h⟩ =>
    have h1 : (![t, ((1 : ℕ) : SyntacticTerm LIinf)] : Fin 2 → SyntacticTerm LIinf) ⟨1, h⟩ =
        ((1 : ℕ) : SyntacticTerm LIinf) := rfl
    rw [h1, numeral_freeVariables] at hx
    exact Finset.notMem_empty x hx

/-! ### The embedded induction axiom -/

section Induction

variable {A : Semisentence LXI 1} {H : Set ThetaNote → Set ThetaNote}

/-- The induction axiom for the body `ψ`, in `LIinf`. -/
def succIndI (ψ : Semiformula LIinf ℕ 1) : Proposition LIinf :=
  (ψ/[numI 0]) 🡒 (∀¹ (ψ/[(#0 : Semiterm LIinf ℕ 1)] 🡒 ψ/[sucI])) 🡒
    ∀¹ (ψ/[(#0 : Semiterm LIinf ℕ 1)])

/-- The body of the existential that the negated induction step is. -/
def stepBody (ψ : Semiformula LIinf ℕ 1) : Semiformula LIinf ℕ 1 :=
  ψ/[(#0 : Semiterm LIinf ℕ 1)] ⋏ ∼(ψ/[sucI])

theorem succInd_eq (φ : Semiformula LXI ℕ 1) :
    succInd φ = (φ/[((0 : ℕ) : SyntacticTerm LXI)]) 🡒
      (∀¹ (φ/[(#0 : Semiterm LXI ℕ 1)] 🡒 φ/[sucX])) 🡒 ∀¹ (φ/[(#0 : Semiterm LXI ℕ 1)]) := rfl

theorem numSubst₁_subst (g : ℕ → ℕ) (s : Semiterm LIinf ℕ 1) (φ : Semiformula LIinf ℕ 1) :
    numSubst₁ g ▹ (φ/[s]) = (numSubst₁ g ▹ φ)/[numSubst₁ g s] := by
  simpa [← comp_app] using smul_ext' (φ := φ) <| by ext x <;> simp [Rew.comp_app, numSubst₁]

theorem numSubst₁_sucI (g : ℕ → ℕ) : numSubst₁ g sucI = sucI := by
  simp [sucI, numSubst₁]

/-- **A numeral assignment passes through the embedded induction axiom.** -/
theorem numSubst_embK_succInd (g : ℕ → ℕ) (φ : Semiformula LXI ℕ 1) :
    numSubst g ▹ embK (succInd φ) = succIndI (numSubst₁ g ▹ embK φ) := by
  rw [succInd_eq, succIndI]
  simp only [Semiformula.imp_eq, embK_or, embK_neg, embK_all, embK_subst₁, embT_numeral,
    embT_sucX, Semiterm.lMap_bvar, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, numSubst_all, numSubst_subst, rew_numeral]
  rw [numSubst₁_subst, numSubst₁_subst, numSubst₁_sucI, numSubst₁_bvar]

/-- Substituting into a substitution instance. -/
theorem subst_subst₁ (ψ : Semiformula LIinf ℕ 1) (s : Semiterm LIinf ℕ 1)
    (t : SyntacticTerm LIinf) : (ψ/[s])/[t] = ψ/[Rew.subst ![t] s] := by
  simpa [← comp_app] using smul_ext' (φ := ψ) <| by ext x <;> simp [Rew.comp_app]

theorem subst_bvar_subst (ψ : Semiformula LIinf ℕ 1) (t : SyntacticTerm LIinf) :
    (ψ/[(#0 : Semiterm LIinf ℕ 1)])/[t] = ψ/[t] := by
  rw [subst_subst₁]; simp

theorem stepBody_inst (ψ : Semiformula LIinf ℕ 1) (n : ℕ) :
    (stepBody ψ)/[numI n] = ψ/[numI n] ⋏ ∼(ψ/[Rew.subst ![numI n] sucI]) := by
  show (Rew.subst ![numI n]) ▹ (ψ/[(#0 : Semiterm LIinf ℕ 1)] ⋏ ∼(ψ/[sucI])) = _
  rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg]
  congr 1
  · exact subst_bvar_subst ψ _
  · exact congrArg _ (subst_subst₁ ψ _ _)

theorem neg_step (ψ : Semiformula LIinf ℕ 1) :
    ∼(∀¹ (ψ/[(#0 : Semiterm LIinf ℕ 1)] 🡒 ψ/[sucI])) = ∃¹ stepBody ψ := by
  simp [stepBody, Semiformula.imp_eq]

theorem params_subst_sub {ψ : Semiformula LIinf ℕ 1} {S : Set ThetaNote}
    (hp : params ψ ⊆ S) {n : ℕ} (t : Semiterm LIinf ℕ n) : params (ψ/[t]) ⊆ S := by
  rw [params_subst]; exact hp

/-- **The chain** (first lecture, proof of Theorem 3.7): from `¬ψ(0)`, the negated induction
step and `ψ(n̄)` in the sequent, a cut-free derivation of height `ω · rk ψ ⊕ 2n`. -/
theorem chain (hA : XFreeL A) (hH : ThetaNote.Nice H) (ψ : Semiformula LIinf ℕ 1)
    (hf : ψ.freeVariables = ∅) (hX : XFreeI ψ) (hp : params ψ ⊆ H ∅) :
    ∀ (n : ℕ) (Γ : Sequent LIinf), ∼(ψ/[numI 0]) ∈ Γ → (∃¹ stepBody ψ) ∈ Γ →
      ψ/[numI n] ∈ Γ → paramsList Γ ⊆ H ∅ →
      IDerivable A ThetaNote.zero H
        (ThetaNote.nadd (ThetaNote.omegaMul (rk ψ)) (ThetaNote.ofNat (2 * n))) Γ := by
  have hK : ∀ t : SyntacticTerm LIinf, ThetaNote.adjoin H (params (ψ/[t])) = H := fun t =>
    ThetaNote.adjoin_eq_self hH.isOperator (params_subst_sub hp t)
  have hrk : ∀ t : SyntacticTerm LIinf, rk (ψ/[t]) = rk ψ := fun t => rk_subst ψ t
  have hmem : ∀ k : ℕ, ThetaNote.nadd (ThetaNote.omegaMul (rk ψ)) (ThetaNote.ofNat k) ∈ H ∅ :=
    fun k => hH.nadd_mem (hH.omegaMul_mem (hH.rk_mem hp)) (hH.ofNat_mem k)
  have taut' : ∀ t : SyntacticTerm LIinf, t.freeVariables = ∅ →
      IDerivable A ThetaNote.zero H (ThetaNote.omegaMul (rk ψ)) [ψ/[t], ∼(ψ/[t])] := by
    intro t ht
    have d := taut (A := A) hH (ψ/[t]) (freeVariables_subst_of_closed ψ hf ht)
    rwa [hK t, hrk t] at d
  intro n
  induction n with
  | zero =>
    intro Γ h0 _ hn hP
    rw [Nat.mul_zero, ThetaNote.ofNat_zero, ThetaNote.nadd_zero]
    refine (taut' (numI 0) (numI_freeVariables 0)).weaken_seq hH.isOperator ?_ hP
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hn
    · exact h0
  | succ n ih =>
    intro Γ h0 hS hn hP
    set inst : Proposition LIinf := (stepBody ψ)/[numI n] with hinst
    have hinst' : inst = ψ/[numI n] ⋏ ∼(ψ/[Rew.subst ![numI n] sucI]) := stepBody_inst ψ n
    have pinst : params inst ⊆ H ∅ := by rw [hinst, params_subst, stepBody, params_and,
      params_neg, params_subst, params_subst, Set.union_self]; exact hp
    have hP1 : paramsList (inst :: Γ) ⊆ H ∅ := by
      rw [paramsList_cons]; exact Set.union_subset pinst hP
    have hP2 : ∀ χ : Proposition LIinf, params χ ⊆ H ∅ → paramsList (χ :: inst :: Γ) ⊆ H ∅ := by
      intro χ hχ; rw [paramsList_cons]; exact Set.union_subset hχ hP1
    -- the left conjunct, from the chain for `n`
    have d1 : IDerivable A ThetaNote.zero H
        (ThetaNote.nadd (ThetaNote.omegaMul (rk ψ)) (ThetaNote.ofNat (2 * n)))
        (ψ/[numI n] :: inst :: Γ) :=
      ih _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h0))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hS)) List.mem_cons_self
        (hP2 _ (params_subst_sub hp _))
    -- the right conjunct, from Lemma 6.1 at the numeral `(n+1)‾` and term replacement
    have hsuc : (Rew.subst ![numI n] sucI).freeVariables = ∅ :=
      freeVariables_subst_sucI (numI_freeVariables n)
    have d2' : IDerivable A ThetaNote.zero H (ThetaNote.omegaMul (rk ψ))
        (∼(ψ/[numI (n + 1)]) :: inst :: Γ) :=
      (taut' (numI (n + 1)) (numI_freeVariables _)).weaken_seq hH.isOperator (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hn)
        · exact List.mem_cons_self) (hP2 _ (by rw [params_neg]; exact params_subst_sub hp _))
    have hsim : Sim (∼(ψ/[numI (n + 1)])) (∼(ψ/[Rew.subst ![numI n] sucI])) := by
      have := sim_subst_closed (n := 0) (φ := ∼ψ) (by rw [Semiformula.freeVariables_not]; exact hf)
        ((xFreeI_neg ψ).mpr hX) (numI_freeVariables (n + 1)) hsuc (fun e ε => by
          rw [val_subst_sucI, val_numI, val_numI])
      simpa using this
    have d2 : IDerivable A ThetaNote.zero H (ThetaNote.omegaMul (rk ψ))
        (∼(ψ/[Rew.subst ![numI n] sucI]) :: inst :: Γ) :=
      d2'.replace_head hA hH.isOperator hsim
    have hlt1 : ThetaNote.nadd (ThetaNote.omegaMul (rk ψ)) (ThetaNote.ofNat (2 * n)) <
        ThetaNote.nadd (ThetaNote.omegaMul (rk ψ)) (ThetaNote.ofNat (2 * n + 1)) :=
      ThetaNote.nadd_ofNat_lt_nadd_ofNat _ (by omega)
    have hlt2 : ThetaNote.omegaMul (rk ψ) <
        ThetaNote.nadd (ThetaNote.omegaMul (rk ψ)) (ThetaNote.ofNat (2 * n + 1)) :=
      ThetaNote.lt_nadd_ofNat_succ _ _
    have d3 : IDerivable A ThetaNote.zero H
        (ThetaNote.nadd (ThetaNote.omegaMul (rk ψ)) (ThetaNote.ofNat (2 * n + 1)))
        (inst :: Γ) :=
      .and (hmem _) hP1 (by rw [← hinst']; exact List.mem_cons_self) hlt1 hlt2 d1 d2
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    exact .exs n (hmem _) hP hS (lt_of_lt_of_le (ThetaNote.ofNat_lt_ofNat (by omega))
      (ThetaNote.le_nadd_right _ _)) (ThetaNote.nadd_ofNat_lt_nadd_ofNat _ (by omega)) d3

/-- **The induction axiom for a body without free variables**, cut-free, at height
`ω · rk ψ ⊕ ω ⊕ 4`. -/
theorem succIndI_derivable (hA : XFreeL A) (hH : ThetaNote.Nice H) (ψ : Semiformula LIinf ℕ 1)
    (hf : ψ.freeVariables = ∅) (hX : XFreeI ψ) (hp : params ψ ⊆ H ∅) :
    IDerivable A ThetaNote.zero H
      (ThetaNote.nadd (ThetaNote.nadd (ThetaNote.omegaMul (rk ψ)) omegaT) (ThetaNote.ofNat 4))
      [succIndI ψ] := by
  set hω : ThetaNote := ThetaNote.nadd (ThetaNote.omegaMul (rk ψ)) omegaT with hhω
  have hmem : ∀ k : ℕ, ThetaNote.nadd hω (ThetaNote.ofNat k) ∈ H ∅ := fun k =>
    hH.nadd_mem (hH.nadd_mem (hH.omegaMul_mem (hH.rk_mem hp)) (hH.omegaPow_mem hH.one_mem))
      (hH.ofNat_mem k)
  have hlt : ∀ j k : ℕ, j < k → ThetaNote.nadd hω (ThetaNote.ofNat j) <
      ThetaNote.nadd hω (ThetaNote.ofNat k) := fun j k h => ThetaNote.nadd_ofNat_lt_nadd_ofNat _ h
  have h0 : ThetaNote.nadd hω (ThetaNote.ofNat 0) = hω := by
    rw [ThetaNote.ofNat_zero, ThetaNote.nadd_zero]
  have hone : ∀ k, ThetaNote.one < ThetaNote.nadd hω (ThetaNote.ofNat k) := fun k =>
    lt_of_lt_of_le (by rw [← ThetaNote.ofNat_one]; exact ThetaNote.ofNat_lt_omega 1)
      (le_trans (ThetaNote.le_nadd_right _ _) (ThetaNote.le_nadd_left _ _))
  set Z : Proposition LIinf := ∼(ψ/[numI 0]) with hZ
  set S : Proposition LIinf := ∃¹ stepBody ψ with hS
  set U : Proposition LIinf := ∀¹ (ψ/[(#0 : Semiterm LIinf ℕ 1)]) with hU
  have eM : succIndI ψ = Z ⋎ (S ⋎ U) := by
    rw [succIndI, Semiformula.imp_eq, Semiformula.imp_eq, neg_step]
  have pZ : params Z ⊆ H ∅ := by rw [hZ, params_neg]; exact params_subst_sub hp _
  have pS : params S ⊆ H ∅ := by
    rw [hS, params_exs, stepBody, params_and, params_neg, params_subst, params_subst,
      Set.union_self]; exact hp
  have pU : params U ⊆ H ∅ := by rw [hU, params_all]; exact params_subst_sub hp _
  have pM : params (succIndI ψ) ⊆ H ∅ := by
    rw [eM, params_or, params_or]; exact Set.union_subset pZ (Set.union_subset pS pU)
  have pl : ∀ Γ : Sequent LIinf, (∀ χ ∈ Γ, params χ ⊆ H ∅) → paramsList Γ ⊆ H ∅ := by
    intro Γ h x ⟨χ, hχ, hx⟩; exact h χ hχ hx
  -- the ω-rule
  have dω : IDerivable A ThetaNote.zero H hω [U, Z, S, S ⋎ U, succIndI ψ] := by
    refine .all (fun n => ThetaNote.nadd (ThetaNote.omegaMul (rk ψ))
      (ThetaNote.ofNat (2 * n))) (by rw [← h0]; exact hmem 0) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl | rfl | rfl
        · exact pU
        · exact pZ
        · exact pS
        · rw [params_or]; exact Set.union_subset pS pU
        · exact pM)) List.mem_cons_self
      (fun n => ThetaNote.nadd_lt_nadd_right _ (ThetaNote.ofNat_lt_omega _)) (fun n => ?_)
    rw [subst_bvar_subst]
    refine chain hA hH ψ hf hX hp n _ ?_ ?_ List.mem_cons_self ?_
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self))
    · refine pl _ ?_
      intro χ hχ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
      rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl
      · exact params_subst_sub hp _
      · exact pU
      · exact pZ
      · exact pS
      · rw [params_or]; exact Set.union_subset pS pU
      · exact pM
  have pSU : params (S ⋎ U) ⊆ H ∅ := by rw [params_or]; exact Set.union_subset pS pU
  have d1 : IDerivable A ThetaNote.zero H (ThetaNote.nadd hω (ThetaNote.ofNat 1))
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
      (ThetaNote.lt_nadd_ofNat_succ hω 0) dω
  have d2 : IDerivable A ThetaNote.zero H (ThetaNote.nadd hω (ThetaNote.ofNat 2))
      [Z, S ⋎ U, succIndI ψ] :=
    .orL (hmem 2) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl
        · exact pZ
        · exact pSU
        · exact pM))
      (List.mem_cons_of_mem _ List.mem_cons_self) (hlt 1 2 (by omega))
      (d1.weaken_seq hH.isOperator (by
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
  have d3 : IDerivable A ThetaNote.zero H (ThetaNote.nadd hω (ThetaNote.ofNat 3))
      [Z, succIndI ψ] :=
    .orR (hmem 3) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl
        · exact pZ
        · exact pM))
      (by rw [eM]; exact List.mem_cons_of_mem _ List.mem_cons_self) (hone 3)
      (hlt 2 3 (by omega))
      (d2.weaken_seq hH.isOperator (by
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

/-- `ω · rk φ ⪯ Ω ⊕ ω · c`, `c` the complexity of `φ`. -/
theorem omegaMul_rk_le {ξ : Type*} {n : ℕ} (φ : Semiformula LIinf ξ n) :
    ThetaNote.omegaMul (rk φ) ≤
      ThetaNote.nadd ThetaNote.Omega (ThetaNote.omegaMul (ThetaNote.ofNat φ.complexity)) := by
  rw [← ThetaNote.omegaMul_Omega, ← ThetaNote.omegaMul_nadd]
  exact ThetaNote.omegaMul_le_omegaMul (rk_le_Omega_nadd φ)

theorem omegaMul_ofNat_lt_Omega (c : ℕ) :
    ThetaNote.omegaMul (ThetaNote.ofNat c) < ThetaNote.Omega :=
  ThetaNote.omegaMul_lt_prin trivial (ThetaNote.ofNat_lt_prin (p := ThetaNote.Omega) trivial c)

/-- `Ω ⊕ y ⪯ Ω · 2` for `y ≺ Ω`. -/
theorem nadd_Omega_le_OmegaTwo {y : ThetaNote} (hy : y < ThetaNote.Omega) (n : ℕ) :
    ThetaNote.nadd ThetaNote.Omega y ≤ ThetaNote.nadd OmegaTwo (ThetaNote.ofNat n) :=
  le_trans (ThetaNote.nadd_le_nadd_right _ (le_of_lt hy)) (ThetaNote.le_nadd_left _ _)

end Bounds

/-! ### The induction axioms -/

section InductionAxiom

variable {A : Semisentence LXI 1}

/-- Numerals of `LXI`. -/
abbrev numX (m : ℕ) : SyntacticTerm LXI := Semiterm.numeral m

theorem embK_rewrite_numX (g : ℕ → ℕ) (ψ : Proposition LXI) :
    embK (Rew.rewrite (fun x => numX (g x)) ▹ ψ) = numSubst g ▹ embK ψ := by
  rw [embK, killX_rew, embed, Semiformula.lMap_rewrite, embK, embed, numSubst]
  have e : (Semiterm.lMap (stageHom Stage.top) ∘ fun x => numX (g x)) = fun x => numI (g x) := by
    funext x; exact embT_numeral (g x)
  rw [e]

theorem emb_embK_univCl (ψ : Proposition LXI) :
    (Rewriting.emb (embK (Semiformula.univCl ψ)) : Proposition LIinf) =
      ∀¹* (embK (Rew.fixitr 0 ψ.fvSup ▹ ψ)) := by
  rw [← embK_emb, Semiformula.coe_univCl_eq_univCl', Semiformula.univCl', embK_allClosure]

theorem embK_fixitr_inst (ψ : Proposition LXI) (w : Fin (0 + ψ.fvSup) → ℕ) :
    (embK (Rew.fixitr 0 ψ.fvSup ▹ ψ) ⇜ fun i => numI (w i)) =
      numSubst (fun y => if hy : y < 0 + ψ.fvSup then w ⟨y, hy⟩ else 0) ▹ embK ψ := by
  have e1 : (fun i : Fin (0 + ψ.fvSup) => numI (w i)) =
      embT ∘ (fun i : Fin (0 + ψ.fvSup) => numX (w i)) := by
    funext i; exact (embT_numeral (w i)).symm
  rw [e1, ← embK_subst, ← embK_rewrite_numX]
  congr 1
  have e2 : (fun i : Fin (0 + ψ.fvSup) => numX (w i)) =
      fun i : Fin (0 + ψ.fvSup) =>
        (fun y => numX (if hy : y < 0 + ψ.fvSup then w ⟨y, hy⟩ else 0)) (i : ℕ) := by
    funext i
    simp only [dif_pos i.isLt, Fin.eta]
  rw [e2]
  exact Semiformula.subst_comp_fixitr_eq_map ψ
    (fun y => numX (if hy : y < 0 + ψ.fvSup then w ⟨y, hy⟩ else 0))

/-- **Every induction axiom of `paLXI`** (Freund, proof of Theorem 6.5, after Theorem 3.7 of
the first lecture): cut-free, at a height below `Ω · 2`. -/
theorem induction_axiom (hA : XFreeL A) {σ : Sentence LXI}
    (h : σ ∈ InductionScheme LXI Set.univ) : AxDerivable A σ := by
  obtain ⟨φ, -, rfl⟩ := h
  set ψ0 : Proposition LXI := succInd φ with hψ0
  set β : ThetaNote := ThetaNote.nadd (ThetaNote.nadd (ThetaNote.omegaMul (rk (embK φ))) omegaT)
    (ThetaNote.ofNat 4) with hβ
  refine axDerivable_of_le 0 (ThetaNote.nadd β (ThetaNote.ofNat (0 + ψ0.fvSup))) ?_
    (fun H hH => ?_)
  · have h1 : β ≤ ThetaNote.nadd (ThetaNote.nadd (ThetaNote.nadd ThetaNote.Omega
        (ThetaNote.omegaMul (ThetaNote.ofNat (embK φ).complexity))) omegaT) (ThetaNote.ofNat 4) :=
      ThetaNote.nadd_le_nadd_left' _ (ThetaNote.nadd_le_nadd_left' _ (omegaMul_rk_le _))
    refine le_trans (ThetaNote.nadd_le_nadd_left' _ h1) ?_
    rw [ThetaNote.nadd_assoc, ThetaNote.nadd_assoc, ThetaNote.nadd_assoc]
    refine nadd_Omega_le_OmegaTwo ?_ 0
    exact ThetaNote.nadd_lt_Omega (omegaMul_ofNat_lt_Omega _)
      (ThetaNote.nadd_lt_Omega (ThetaNote.omegaPow_lt_Omega
        (ThetaNote.one_lt_prin (p := ThetaNote.Omega) trivial))
        (ThetaNote.nadd_lt_Omega (ThetaNote.ofNat_lt_prin (p := ThetaNote.Omega) trivial _)
          (ThetaNote.ofNat_lt_prin (p := ThetaNote.Omega) trivial _)))
  · have hΩ : ThetaNote.Omega ∈ H ∅ := hH.Omega_mem
    have hpK : ∀ {m : ℕ} (χ : Semiformula LXI ℕ m), params (embK χ) ⊆ H ∅ := fun χ =>
      (params_embK χ).trans (Set.singleton_subset_iff.mpr hΩ)
    rw [emb_embK_univCl]
    refine allClosure_derivable hH.isOperator _ (fun j => hH.nadd_mem (hH.nadd_mem
      (hH.nadd_mem (hH.omegaMul_mem (hH.rk_mem (hpK φ))) (hH.omegaPow_mem hH.one_mem))
      (hH.ofNat_mem 4)) (hH.ofNat_mem j)) (hpK _) (fun w => ?_)
    rw [embK_fixitr_inst, numSubst_embK_succInd]
    set g : ℕ → ℕ := fun y => if hy : y < 0 + ψ0.fvSup then w ⟨y, hy⟩ else 0 with hg
    have d := succIndI_derivable hA hH (numSubst₁ g ▹ embK φ) (freeVariables_numSubst₁ g _)
      ((xFreeI_rew (numSubst₁ g) _).mpr (xFreeI_embK φ)) (by rw [params_rew]; exact hpK φ)
    rwa [rk_rew] at d

end InductionAxiom

end InductiveDef

end OrdinalAnalysis
