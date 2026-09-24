/-
  Closed terms and their values in the infinitary calculus of `ID₁`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §6: the remark in the proof of Proposition 6.4
  ("we can replace any occurrence of `t` by the numeral with the same value, since the
  notion of false literal in Definition 5.1 is unaffected"), used again for the
  existential quantifier in the proof of Theorem 6.5; after Exercise 3.5 of the first
  lecture.

  **No evaluator.**  The calculus instantiates a quantifier `∀x ψ(x)` at the numerals
  `ψ(n̄)`, not at evaluated instances, so no normalisation of closed terms is built into
  it.  What the embedding needs instead is Freund's remark: a derivation of `Γ` stays a
  derivation, at the same height, cut rank and operator, when closed terms are replaced
  by closed terms of the same value.  The rules that inspect a closed term only through
  its value are the arithmetic literals (Definition 5.1: a literal is true or false by
  the value of its arguments); the stage rules and (Fix) carry the term into the premise
  `A(t, I^{≺γ})` unchanged, and the quantifier rules substitute numerals, which commutes
  with the replacement.

  One rule of the calculus as built is *not* blind to terms: the identity clause `idX` for
  the free predicate `X` asks for literally the same term in `X t` and `¬X t`, and
  Freund's language has no `X`.  So the replacement is allowed at arithmetic and stage
  literals only; a literal `X t` must stay as it is (`RelOK`).  The operator form `A` is
  then required to be `X`-free (`XFreeL A`), since the stage rules move the term into
  `A(t, I^{≺γ})`.

  **The relation.**  `TEq s t`: `s = t`, or both are free of free variables and have the
  same value under every assignment.  `Sim φ ψ`: `ψ` is `φ` with some arguments of
  arithmetic and stage literals replaced by `TEq`-related terms.  Then

      H ⊢^α_ρ Γ,  every formula of Γ is Sim-related to a formula of Γ'
        ⇒  H ⊢^α_ρ Γ'                                           (`IDerivable.replace`),

  which also contains weakening in the sequent.

  Contents.

    `lMap_toLIinf_numeral`, `val_numI`       a numeral denotes its value
    `closedVal`, `val_closed`                the value of a closed term
    `le_omegaMul`                            `α ⪯ ω · α` (by well-foundedness)
    `IsXRel`, `XFreeI`, `XFreeL`             formulas without the free predicate `X`
    `TEq`, `RelOK`, `Sim`                    the replacement relation
    `Sim.refl`, `Sim.neg`, `Sim.params_eq`, `Sim.rew`, `Sim.trueLit`
    `Sim.of_rew_pair`                        two closed instances of the same formula
    `sim_subst_closed`, `sim_subst_numI`     `ψ(s) ~ ψ(t)` for closed `s`, `t` of equal value
    `IDerivable.replace`, `replace_head`     **term replacement**
-/
import OrdinalAnalysis.ID1.Calculus

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

open LO LO.FirstOrder

/-! ### Numerals denote their values -/

section Numeral

variable {ξ : Type*} {n : ℕ}

private lemma lMapNumI_zero :
    Semiterm.lMap toLIinf ((0 : ℕ) : Semiterm ℒₒᵣ ξ n) = ((0 : ℕ) : Semiterm LIinf ξ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, toLIinf]

private lemma lMapNumI_one :
    Semiterm.lMap toLIinf ((1 : ℕ) : Semiterm ℒₒᵣ ξ n) = ((1 : ℕ) : Semiterm LIinf ξ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, toLIinf]

private lemma lMapNumI_add (v : Fin 2 → Semiterm ℒₒᵣ ξ n) :
    Semiterm.lMap toLIinf (Semiterm.Operator.Add.add.operator v) =
      Semiterm.Operator.Add.add.operator (Semiterm.lMap toLIinf ∘ v) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, toLIinf]
  funext i
  simp

private lemma numeralI_succ_succ (L : Language) [L.Zero] [L.One] [L.Add] (k : ℕ) :
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

/-- The numerals of `LIinf` are the numerals of arithmetic. -/
theorem lMap_toLIinf_numeral (k : ℕ) :
    Semiterm.lMap toLIinf ((k : ℕ) : Semiterm ℒₒᵣ ξ n) = ((k : ℕ) : Semiterm LIinf ξ n) := by
  induction k with
  | zero => exact lMapNumI_zero
  | succ k ih =>
    cases k with
    | zero => exact lMapNumI_one
    | succ k =>
      rw [numeralI_succ_succ ℒₒᵣ k, numeralI_succ_succ LIinf k, lMapNumI_add]
      congr 1
      funext i
      match i with
      | ⟨0, _⟩ => exact ih
      | ⟨1, _⟩ => exact lMapNumI_one

/-- **A numeral denotes its value** in the standard structure. -/
@[simp] theorem val_numeral_stdInf (m : ℕ) (e : Fin n → ℕ) (ε : ξ → ℕ) :
    Semiterm.val (s := stdInf) e ε ((m : ℕ) : Semiterm LIinf ξ n) = m := by
  rw [← lMap_toLIinf_numeral m]
  show Semiterm.val (s := Structure.add ℒₒᵣ IInfLang ℕ (str₂ := iinfFalse)) e ε
    (Semiterm.lMap (Language.Hom.add₁ ℒₒᵣ IInfLang) ((m : ℕ) : Semiterm ℒₒᵣ ξ n)) = m
  rw [Structure.val_lMap_add₁ (str₂ := iinfFalse)]
  simp

@[simp] theorem val_numI (m : ℕ) (e : Fin 0 → ℕ) (ε : ℕ → ℕ) :
    Semiterm.val (s := stdInf) e ε (numI m) = m :=
  val_numeral_stdInf m e ε

/-- A numeral at any level has no free variable. -/
theorem numeral_freeVariables (m : ℕ) : ((m : ℕ) : Semiterm LIinf ℕ n).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hx' : ((Rew.subst ![]) (Rew.emb (Semiterm.Operator.numeral LIinf m).term) :
      Semiterm LIinf ℕ n).FVar? x := hx
  rcases Semiterm.fvar?_rew hx' with ⟨i, -⟩ | ⟨z, hz, -⟩
  · exact i.elim0
  · have hz' : z ∈ (Rew.emb (Semiterm.Operator.numeral LIinf m).term :
        Semiterm LIinf ℕ 0).freeVariables := hz
    simp at hz'

theorem numI_freeVariables (m : ℕ) : (numI m).freeVariables = ∅ := numeral_freeVariables m

/-- Every rewriting fixes a numeral. -/
@[simp] theorem rew_numeral {n₁ n₂ : ℕ} (ω : Rew LIinf ℕ n₁ ℕ n₂) (m : ℕ) :
    ω ((m : ℕ) : Semiterm LIinf ℕ n₁) = ((m : ℕ) : Semiterm LIinf ℕ n₂) := by
  simp

end Numeral

/-! ### The value of a closed term -/

/-- The value of a closed term in the standard structure. -/
def closedVal (t : SyntacticTerm LIinf) : ℕ :=
  Semiterm.val (s := stdInf) ![] (fun _ => 0) t

/-- The value of a term without free variables does not depend on the assignment. -/
theorem val_closed {t : SyntacticTerm LIinf} (ht : t.freeVariables = ∅) (e : Fin 0 → ℕ)
    (ε : ℕ → ℕ) : Semiterm.val (s := stdInf) e ε t = closedVal t := by
  unfold closedVal
  have he : e = ![] := funext fun i => i.elim0
  subst he
  refine Semiterm.val_eq_of_funEqOn t ?_
  intro x hx
  have hx' : x ∈ t.freeVariables := hx
  rw [ht] at hx'
  exact absurd hx' (Finset.notMem_empty x)

@[simp] theorem closedVal_numI (m : ℕ) : closedVal (numI m) = m := val_numI m ![] _

/-! ### `α ⪯ ω · α` -/

/-- **`α ⪯ ω · α`**: a strictly increasing map of a well-order is inflationary. -/
theorem ThetaNote.le_omegaMul (a : ThetaNote) : a ≤ ThetaNote.omegaMul a := by
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    by_contra h
    have hlt : ThetaNote.omegaMul a < a := lt_of_not_ge h
    have h1 := ih _ hlt
    exact absurd (ThetaNote.omegaMul_lt_omegaMul hlt) (not_lt_of_ge h1)

/-! ### Formulas without `X` -/

/-- `r` is the free predicate `X`. -/
def IsXRel : {k : ℕ} → LIinf.Rel k → Prop
  | _, Sum.inl _ => False
  | _, Sum.inr IInfRel.X => True
  | _, Sum.inr (IInfRel.stage _) => False

/-- A formula of `LIinf` without the free predicate `X`. -/
def XFreeI {ξ : Type*} : {n : ℕ} → Semiformula LIinf ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel r _ => ¬IsXRel r
  | _, .nrel r _ => ¬IsXRel r
  | _, .and φ ψ => XFreeI φ ∧ XFreeI ψ
  | _, .or φ ψ => XFreeI φ ∧ XFreeI ψ
  | _, .all φ => XFreeI φ
  | _, .exs φ => XFreeI φ

/-- A formula of `LXI` without the free predicate `X`. -/
def XFreeL {ξ : Type*} : {n : ℕ} → Semiformula LXI ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel (Sum.inl _) _ => True
  | _, .rel (Sum.inr IXRel.X) _ => False
  | _, .rel (Sum.inr IXRel.I) _ => True
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr IXRel.X) _ => False
  | _, .nrel (Sum.inr IXRel.I) _ => True
  | _, .and φ ψ => XFreeL φ ∧ XFreeL ψ
  | _, .or φ ψ => XFreeL φ ∧ XFreeL ψ
  | _, .all φ => XFreeL φ
  | _, .exs φ => XFreeL φ

section XFree

variable {ξ : Type*}

@[simp] theorem xFreeI_neg {n : ℕ} (φ : Semiformula LIinf ξ n) : XFreeI (∼φ) ↔ XFreeI φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v => exact Iff.rfl
  | hnrel r v => exact Iff.rfl
  | hand φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | hor φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | hall φ ih => exact ih
  | hexs φ ih => exact ih

@[simp] theorem xFreeI_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LIinf ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformula LIinf ξ₁ n₁) : XFreeI (ω ▹ φ) ↔ XFreeI φ := by
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => simp only [LogicalConnective.HomClass.map_top]; exact Iff.rfl
  | hfalsum => simp only [LogicalConnective.HomClass.map_bot]; exact Iff.rfl
  | hrel r v => rw [Semiformula.rew_rel]; exact Iff.rfl
  | hnrel r v => rw [Semiformula.rew_nrel]; exact Iff.rfl
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and]; exact and_congr (ihφ ω) (ihψ ω)
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or]; exact and_congr (ihφ ω) (ihψ ω)
  | hall φ ih => rw [Rewriting.app_all]; exact ih ω.q
  | hexs φ ih => rw [Rewriting.app_exs]; exact ih ω.q

theorem xFreeI_lMap_stageHom (a : Stage) {m : ℕ} :
    ∀ (φ : Semiformula LXI ξ m), XFreeL φ → XFreeI (Semiformula.lMap (stageHom a) φ)
  | .verum, _ => trivial
  | .falsum, _ => trivial
  | .rel (Sum.inl _) _, _ => fun h => h
  | .rel (Sum.inr IXRel.X) _, h => h.elim
  | .rel (Sum.inr IXRel.I) _, _ => fun h => h
  | .nrel (Sum.inl _) _, _ => fun h => h
  | .nrel (Sum.inr IXRel.X) _, h => h.elim
  | .nrel (Sum.inr IXRel.I) _, _ => fun h => h
  | .and φ ψ, h => ⟨xFreeI_lMap_stageHom a φ h.1, xFreeI_lMap_stageHom a ψ h.2⟩
  | .or φ ψ, h => ⟨xFreeI_lMap_stageHom a φ h.1, xFreeI_lMap_stageHom a ψ h.2⟩
  | .all φ, h => xFreeI_lMap_stageHom a φ h
  | .exs φ, h => xFreeI_lMap_stageHom a φ h

/-- For an `X`-free operator form, every unfolding is `X`-free. -/
theorem xFreeI_unfold_body {A : Semisentence LXI 1} (hA : XFreeL A) (a : Stage) :
    XFreeI (Rew.emb ▹ formAt A a : Semiformula LIinf ℕ 1) :=
  (xFreeI_rew _ _).mpr (xFreeI_lMap_stageHom a A hA)

end XFree

/-! ### The replacement relation -/

/-- `s` and `t` are equal, or both are free of free variables and have the same value under
every assignment. -/
def TEq {n : ℕ} (s t : Semiterm LIinf ℕ n) : Prop :=
  s = t ∨ (s.freeVariables = ∅ ∧ t.freeVariables = ∅ ∧
    ∀ (e : Fin n → ℕ) (ε : ℕ → ℕ),
      Semiterm.val (s := stdInf) e ε s = Semiterm.val (s := stdInf) e ε t)

/-- The arguments of a literal may be replaced, unless the literal is an `X`-literal. -/
def RelOK {n k : ℕ} (r : LIinf.Rel k) (v w : Fin k → Semiterm LIinf ℕ n) : Prop :=
  v = w ∨ (¬IsXRel r ∧ ∀ i, TEq (v i) (w i))

/-- **`Sim φ ψ`**: `ψ` is `φ` with some arguments of arithmetic and stage literals replaced by
`TEq`-related terms. -/
def Sim : {n : ℕ} → Semiformula LIinf ℕ n → Semiformula LIinf ℕ n → Prop
  | _, .verum, ψ => ψ = ⊤
  | _, .falsum, ψ => ψ = ⊥
  | _, .rel r v, ψ => ∃ w, ψ = .rel r w ∧ RelOK r v w
  | _, .nrel r v, ψ => ∃ w, ψ = .nrel r w ∧ RelOK r v w
  | _, .and φ₁ φ₂, ψ => ∃ ψ₁ ψ₂, ψ = ψ₁ ⋏ ψ₂ ∧ Sim φ₁ ψ₁ ∧ Sim φ₂ ψ₂
  | _, .or φ₁ φ₂, ψ => ∃ ψ₁ ψ₂, ψ = ψ₁ ⋎ ψ₂ ∧ Sim φ₁ ψ₁ ∧ Sim φ₂ ψ₂
  | _, .all φ, ψ => ∃ ψ', ψ = ∀¹ ψ' ∧ Sim φ ψ'
  | _, .exs φ, ψ => ∃ ψ', ψ = ∃¹ ψ' ∧ Sim φ ψ'

section Sim

theorem TEq.refl {n : ℕ} (t : Semiterm LIinf ℕ n) : TEq t t := Or.inl rfl

theorem RelOK.refl {n k : ℕ} (r : LIinf.Rel k) (v : Fin k → Semiterm LIinf ℕ n) : RelOK r v v :=
  Or.inl rfl

theorem Sim.refl {n : ℕ} (φ : Semiformula LIinf ℕ n) : Sim φ φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact rfl
  | hfalsum => exact rfl
  | hrel r v => exact ⟨v, rfl, RelOK.refl r v⟩
  | hnrel r v => exact ⟨v, rfl, RelOK.refl r v⟩
  | hand φ ψ ihφ ihψ => exact ⟨φ, ψ, rfl, ihφ, ihψ⟩
  | hor φ ψ ihφ ihψ => exact ⟨φ, ψ, rfl, ihφ, ihψ⟩
  | hall φ ih => exact ⟨φ, rfl, ih⟩
  | hexs φ ih => exact ⟨φ, rfl, ih⟩

theorem Sim.neg {n : ℕ} {φ ψ : Semiformula LIinf ℕ n} (h : Sim φ ψ) : Sim (∼φ) (∼ψ) := by
  induction φ using Semiformula.rec' with
  | hverum => obtain rfl : ψ = ⊤ := h; exact rfl
  | hfalsum => obtain rfl : ψ = ⊥ := h; exact rfl
  | hrel r v =>
    obtain ⟨w, rfl, hw⟩ := h
    exact ⟨w, rfl, hw⟩
  | hnrel r v =>
    obtain ⟨w, rfl, hw⟩ := h
    exact ⟨w, rfl, hw⟩
  | hand φ₁ φ₂ ih₁ ih₂ =>
    obtain ⟨ψ₁, ψ₂, rfl, h₁, h₂⟩ := h
    exact ⟨∼ψ₁, ∼ψ₂, rfl, ih₁ h₁, ih₂ h₂⟩
  | hor φ₁ φ₂ ih₁ ih₂ =>
    obtain ⟨ψ₁, ψ₂, rfl, h₁, h₂⟩ := h
    exact ⟨∼ψ₁, ∼ψ₂, rfl, ih₁ h₁, ih₂ h₂⟩
  | hall φ ih =>
    obtain ⟨ψ', rfl, h'⟩ := h
    exact ⟨∼ψ', rfl, ih h'⟩
  | hexs φ ih =>
    obtain ⟨ψ', rfl, h'⟩ := h
    exact ⟨∼ψ', rfl, ih h'⟩

/-- Replacing terms does not change the parameters. -/
theorem Sim.params_eq {n : ℕ} {φ ψ : Semiformula LIinf ℕ n} (h : Sim φ ψ) :
    params ψ = params φ := by
  induction φ using Semiformula.rec' with
  | hverum => obtain rfl : ψ = ⊤ := h; rfl
  | hfalsum => obtain rfl : ψ = ⊥ := h; rfl
  | hrel r v => obtain ⟨w, rfl, -⟩ := h; rfl
  | hnrel r v => obtain ⟨w, rfl, -⟩ := h; rfl
  | hand φ₁ φ₂ ih₁ ih₂ =>
    obtain ⟨ψ₁, ψ₂, rfl, h₁, h₂⟩ := h
    rw [params_and, params_and, ih₁ h₁, ih₂ h₂]
  | hor φ₁ φ₂ ih₁ ih₂ =>
    obtain ⟨ψ₁, ψ₂, rfl, h₁, h₂⟩ := h
    rw [params_or, params_or, ih₁ h₁, ih₂ h₂]
  | hall φ ih => obtain ⟨ψ', rfl, h'⟩ := h; exact ih h'
  | hexs φ ih => obtain ⟨ψ', rfl, h'⟩ := h; exact ih h'

/-- A rewriting whose bound-variable images have no free variables keeps a term without
free variables free of them. -/
theorem freeVariables_rew_term {n₁ n₂ : ℕ} (ω : Rew LIinf ℕ n₁ ℕ n₂)
    (hb : ∀ x, (ω #x).freeVariables = ∅) :
    ∀ {t : Semiterm LIinf ℕ n₁}, t.freeVariables = ∅ → (ω t).freeVariables = ∅ := by
  intro t ht
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiterm.fvar?_rew (ω := ω) (t := t) (x := x) hx with ⟨i, hi⟩ | ⟨z, hz, _⟩
  · have hi' : x ∈ (ω #i).freeVariables := hi
    rw [hb i] at hi'
    exact Finset.notMem_empty x hi'
  · have hz' : z ∈ t.freeVariables := hz
    rw [ht] at hz'
    exact Finset.notMem_empty z hz'

theorem freeVariables_bShift {n : ℕ} (t : Semiterm LIinf ℕ n) :
    (Rew.bShift t).freeVariables = t.freeVariables := by
  ext x
  exact Semiterm.fvar?_bShift

/-- The rewritings that keep `Sim`: the bound variables go to terms without free
variables. -/
def BClosed {n₁ n₂ : ℕ} (ω : Rew LIinf ℕ n₁ ℕ n₂) : Prop :=
  ∀ x, (ω #x).freeVariables = ∅

theorem BClosed.q {n₁ n₂ : ℕ} {ω : Rew LIinf ℕ n₁ ℕ n₂} (h : BClosed ω) : BClosed ω.q := by
  intro x
  cases x using Fin.cases with
  | zero => rw [Rew.q_bvar_zero]; rfl
  | succ x => rw [Rew.q_bvar_succ, freeVariables_bShift]; exact h x

theorem TEq.rew {n₁ n₂ : ℕ} {ω : Rew LIinf ℕ n₁ ℕ n₂} (hω : BClosed ω)
    {s t : Semiterm LIinf ℕ n₁} (h : TEq s t) : TEq (ω s) (ω t) := by
  rcases h with rfl | ⟨hs, ht, hv⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨freeVariables_rew_term ω hω hs, freeVariables_rew_term ω hω ht, ?_⟩
    intro e ε
    rw [Semiterm.val_rew, Semiterm.val_rew]
    exact hv _ _

theorem RelOK.rew {n₁ n₂ k : ℕ} {ω : Rew LIinf ℕ n₁ ℕ n₂} (hω : BClosed ω) {r : LIinf.Rel k}
    {v w : Fin k → Semiterm LIinf ℕ n₁} (h : RelOK r v w) : RelOK r (ω ∘ v) (ω ∘ w) := by
  rcases h with rfl | ⟨hr, h⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hr, fun i => (h i).rew hω⟩

/-- **`Sim` is stable under rewritings whose bound-variable images have no free variables**,
in particular under the instantiation of a quantifier at a numeral. -/
theorem Sim.rew {n₁ : ℕ} {φ ψ : Semiformula LIinf ℕ n₁} (h : Sim φ ψ) :
    ∀ {n₂ : ℕ} {ω : Rew LIinf ℕ n₁ ℕ n₂}, BClosed ω → Sim (ω ▹ φ) (ω ▹ ψ) := by
  induction φ using Semiformula.rec' with
  | hverum =>
    intro n₂ ω _; obtain rfl : ψ = ⊤ := h
    simp only [LogicalConnective.HomClass.map_top]; exact rfl
  | hfalsum =>
    intro n₂ ω _; obtain rfl : ψ = ⊥ := h
    simp only [LogicalConnective.HomClass.map_bot]; exact rfl
  | hrel r v =>
    intro n₂ ω hω
    obtain ⟨w, rfl, hw⟩ := h
    rw [Semiformula.rew_rel, Semiformula.rew_rel]
    exact ⟨_, rfl, hw.rew hω⟩
  | hnrel r v =>
    intro n₂ ω hω
    obtain ⟨w, rfl, hw⟩ := h
    rw [Semiformula.rew_nrel, Semiformula.rew_nrel]
    exact ⟨_, rfl, hw.rew hω⟩
  | hand φ₁ φ₂ ih₁ ih₂ =>
    intro n₂ ω hω
    obtain ⟨ψ₁, ψ₂, rfl, h₁, h₂⟩ := h
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact ⟨_, _, rfl, ih₁ h₁ hω, ih₂ h₂ hω⟩
  | hor φ₁ φ₂ ih₁ ih₂ =>
    intro n₂ ω hω
    obtain ⟨ψ₁, ψ₂, rfl, h₁, h₂⟩ := h
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact ⟨_, _, rfl, ih₁ h₁ hω, ih₂ h₂ hω⟩
  | hall φ ih =>
    intro n₂ ω hω
    obtain ⟨ψ', rfl, h'⟩ := h
    rw [Rewriting.app_all, Rewriting.app_all]
    exact ⟨_, rfl, ih h' hω.q⟩
  | hexs φ ih =>
    intro n₂ ω hω
    obtain ⟨ψ', rfl, h'⟩ := h
    rw [Rewriting.app_exs, Rewriting.app_exs]
    exact ⟨_, rfl, ih h' hω.q⟩

theorem bClosed_subst_numI (m : ℕ) :
    BClosed (Rew.subst ![numI m] : Rew LIinf ℕ 1 ℕ 0) := by
  intro x
  cases x using Fin.cases with
  | zero => simpa using numI_freeVariables m
  | succ x => exact x.elim0

theorem Sim.subst_numI {φ ψ : Semiformula LIinf ℕ 1} (h : Sim φ ψ) (m : ℕ) :
    Sim (φ/[numI m]) (ψ/[numI m]) :=
  h.rew (bClosed_subst_numI m)

/-- **The truth of an arithmetic literal sees only the values of its arguments.** -/
theorem Sim.trueLit {φ ψ : Proposition LIinf} (h : Sim φ ψ) (hφ : TrueLit φ) : TrueLit ψ := by
  obtain ⟨⟨k, r, v, hform, hv⟩, htrue⟩ := hφ
  have key : ∀ w : Fin k → SyntacticTerm LIinf, RelOK (Sum.inl r : LIinf.Rel k) v w →
      (∀ i, (w i).freeVariables = ∅) ∧
        (fun i => Semiterm.val (s := stdInf) ![] (fun _ => 0) (v i)) =
          (fun i => Semiterm.val (s := stdInf) ![] (fun _ => 0) (w i)) := by
    intro w hw
    rcases hw with rfl | ⟨-, hw⟩
    · exact ⟨hv, rfl⟩
    · refine ⟨fun i => ?_, funext fun i => ?_⟩
      · rcases hw i with he | ⟨-, hwi, -⟩
        · rw [← he]; exact hv i
        · exact hwi
      · rcases hw i with he | ⟨-, -, hval⟩
        · rw [he]
        · exact hval _ _
  rcases hform with rfl | rfl
  · obtain ⟨w, rfl, hw⟩ := h
    obtain ⟨hw', hval⟩ := key w hw
    refine ⟨⟨k, r, w, Or.inl rfl, hw'⟩, ?_⟩
    have ht : Semiformula.Eval (s := stdInf) ![] (fun _ => 0)
        (Semiformula.rel (Sum.inl r : LIinf.Rel k) v) := htrue
    have hval' : (Semiterm.val (s := stdInf) ![] (fun _ => 0) ∘ v) =
        (Semiterm.val (s := stdInf) ![] (fun _ => 0) ∘ w) := hval
    exact (Semiformula.eval_rel (s := stdInf) (r := (Sum.inl r : LIinf.Rel k))).mpr
      (hval' ▸ (Semiformula.eval_rel (s := stdInf) (r := (Sum.inl r : LIinf.Rel k))).mp ht)
  · obtain ⟨w, rfl, hw⟩ := h
    obtain ⟨hw', hval⟩ := key w hw
    refine ⟨⟨k, r, w, Or.inr rfl, hw'⟩, ?_⟩
    have ht : Semiformula.Eval (s := stdInf) ![] (fun _ => 0)
        (Semiformula.nrel (Sum.inl r : LIinf.Rel k) v) := htrue
    have hval' : (Semiterm.val (s := stdInf) ![] (fun _ => 0) ∘ v) =
        (Semiterm.val (s := stdInf) ![] (fun _ => 0) ∘ w) := hval
    exact (Semiformula.eval_nrel (s := stdInf) (r := (Sum.inl r : LIinf.Rel k))).mpr
      (hval' ▸ (Semiformula.eval_nrel (s := stdInf) (r := (Sum.inl r : LIinf.Rel k))).mp ht)

/-- Two rewritings that send the bound variables to terms without free variables of equal
values, and agree on the free variables. -/
def PairOK {n₁ n₂ : ℕ} (ω ω' : Rew LIinf ℕ n₁ ℕ n₂) : Prop :=
  (∀ x, (ω #x).freeVariables = ∅ ∧ (ω' #x).freeVariables = ∅ ∧
    ∀ (e : Fin n₂ → ℕ) (ε : ℕ → ℕ),
      Semiterm.val (s := stdInf) e ε (ω #x) = Semiterm.val (s := stdInf) e ε (ω' #x)) ∧
  ∀ x, ω &x = ω' &x

theorem PairOK.q {n₁ n₂ : ℕ} {ω ω' : Rew LIinf ℕ n₁ ℕ n₂} (h : PairOK ω ω') :
    PairOK ω.q ω'.q := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · cases x using Fin.cases with
    | zero =>
      rw [Rew.q_bvar_zero, Rew.q_bvar_zero]
      exact ⟨rfl, rfl, fun _ _ => rfl⟩
    | succ x =>
      rw [Rew.q_bvar_succ, Rew.q_bvar_succ, freeVariables_bShift, freeVariables_bShift]
      obtain ⟨h1, h2, h3⟩ := h.1 x
      refine ⟨h1, h2, fun e ε => ?_⟩
      rw [Semiterm.val_bShift', Semiterm.val_bShift']
      exact h3 _ _
  · rw [Rew.q_fvar, Rew.q_fvar, h.2 x]

theorem PairOK.teq {n₁ n₂ : ℕ} {ω ω' : Rew LIinf ℕ n₁ ℕ n₂} (h : PairOK ω ω')
    {t : Semiterm LIinf ℕ n₁} (ht : t.freeVariables = ∅) : TEq (ω t) (ω' t) := by
  refine Or.inr ⟨freeVariables_rew_term ω (fun x => (h.1 x).1) ht,
    freeVariables_rew_term ω' (fun x => (h.1 x).2.1) ht, fun e ε => ?_⟩
  rw [Semiterm.val_rew, Semiterm.val_rew]
  congr 1
  · funext x; exact (h.1 x).2.2 e ε
  · funext x; simp only [Function.comp_apply, h.2 x]

theorem freeVariables_rel_arg {n k : ℕ} {r : LIinf.Rel k} {v : Fin k → Semiterm LIinf ℕ n}
    (h : (Semiformula.rel r v).freeVariables = ∅) (i : Fin k) : (v i).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have : x ∈ (Semiformula.rel r v).freeVariables := by
    rw [Semiformula.freeVariables_rel]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  rw [h] at this
  exact Finset.notMem_empty x this

theorem freeVariables_nrel_arg {n k : ℕ} {r : LIinf.Rel k} {v : Fin k → Semiterm LIinf ℕ n}
    (h : (Semiformula.nrel r v).freeVariables = ∅) (i : Fin k) : (v i).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have : x ∈ (Semiformula.nrel r v).freeVariables := by
    rw [Semiformula.freeVariables_nrel]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  rw [h] at this
  exact Finset.notMem_empty x this

/-- **Two instances of one `X`-free formula** under rewritings that put closed terms of
equal values at the bound variables are `Sim`-related. -/
theorem Sim.of_rew_pair {n₁ : ℕ} {φ : Semiformula LIinf ℕ n₁} (hφ : φ.freeVariables = ∅)
    (hX : XFreeI φ) :
    ∀ {n₂ : ℕ} {ω ω' : Rew LIinf ℕ n₁ ℕ n₂}, PairOK ω ω' → Sim (ω ▹ φ) (ω' ▹ φ) := by
  induction φ using Semiformula.rec' with
  | hverum =>
    intro n₂ ω ω' _
    simp only [LogicalConnective.HomClass.map_top]; exact rfl
  | hfalsum =>
    intro n₂ ω ω' _
    simp only [LogicalConnective.HomClass.map_bot]; exact rfl
  | hrel r v =>
    intro n₂ ω ω' h
    rw [Semiformula.rew_rel, Semiformula.rew_rel]
    exact ⟨_, rfl, Or.inr ⟨hX, fun i => h.teq (freeVariables_rel_arg hφ i)⟩⟩
  | hnrel r v =>
    intro n₂ ω ω' h
    rw [Semiformula.rew_nrel, Semiformula.rew_nrel]
    exact ⟨_, rfl, Or.inr ⟨hX, fun i => h.teq (freeVariables_nrel_arg hφ i)⟩⟩
  | hand φ₁ φ₂ ih₁ ih₂ =>
    intro n₂ ω ω' h
    rw [Semiformula.freeVariables_and, Finset.union_eq_empty] at hφ
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact ⟨_, _, rfl, ih₁ hφ.1 hX.1 h, ih₂ hφ.2 hX.2 h⟩
  | hor φ₁ φ₂ ih₁ ih₂ =>
    intro n₂ ω ω' h
    rw [Semiformula.freeVariables_or, Finset.union_eq_empty] at hφ
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact ⟨_, _, rfl, ih₁ hφ.1 hX.1 h, ih₂ hφ.2 hX.2 h⟩
  | hall φ ih =>
    intro n₂ ω ω' h
    rw [Rewriting.app_all, Rewriting.app_all]
    exact ⟨_, rfl, ih hφ hX h.q⟩
  | hexs φ ih =>
    intro n₂ ω ω' h
    rw [Rewriting.app_exs, Rewriting.app_exs]
    exact ⟨_, rfl, ih hφ hX h.q⟩

/-- **`ψ(s) ~ ψ(t)`** for an `X`-free `ψ` without free variables and closed `s`, `t` of equal
value. -/
theorem sim_subst_closed {n : ℕ} {φ : Semiformula LIinf ℕ 1} (hφ : φ.freeVariables = ∅)
    (hX : XFreeI φ) {s t : Semiterm LIinf ℕ n} (hs : s.freeVariables = ∅)
    (ht : t.freeVariables = ∅)
    (hv : ∀ (e : Fin n → ℕ) (ε : ℕ → ℕ),
      Semiterm.val (s := stdInf) e ε s = Semiterm.val (s := stdInf) e ε t) :
    Sim (Rew.subst ![s] ▹ φ) (Rew.subst ![t] ▹ φ) := by
  refine Sim.of_rew_pair hφ hX ⟨fun x => ?_, fun x => ?_⟩
  · cases x using Fin.cases with
    | zero => simpa using ⟨hs, ht, hv⟩
    | succ x => exact x.elim0
  · simp

/-- **Freund's remark**: a closed term may be replaced by the numeral of its value. -/
theorem sim_subst_numI {φ : Semiformula LIinf ℕ 1} (hφ : φ.freeVariables = ∅) (hX : XFreeI φ)
    {t : SyntacticTerm LIinf} (ht : t.freeVariables = ∅) :
    Sim (φ/[t]) (φ/[numI (closedVal t)]) :=
  sim_subst_closed hφ hX ht (numI_freeVariables _) (fun e ε => by
    rw [val_closed ht, val_numI])

theorem TEq.sim_subst {φ : Semiformula LIinf ℕ 1} (hφ : φ.freeVariables = ∅) (hX : XFreeI φ)
    {t t' : SyntacticTerm LIinf} (h : TEq t t') : Sim (φ/[t]) (φ/[t']) := by
  rcases h with rfl | ⟨hs, ht, hv⟩
  · exact Sim.refl _
  · exact sim_subst_closed hφ hX hs ht hv

end Sim

/-! ### Term replacement -/

section Replace

variable {A : Semisentence LXI 1} {ρ : ThetaNote}

/-- The unfolding at two `TEq`-related terms. -/
theorem sim_unfold (hA : XFreeL A) (g : Stage) {t t' : SyntacticTerm LIinf} (h : TEq t t') :
    Sim (unfold A g t) (unfold A g t') :=
  h.sim_subst (Semiformula.freeVariables_emb _) (xFreeI_unfold_body hA g)

theorem stage_sim {a : Stage} {t : SyntacticTerm LIinf} {φ' : Proposition LIinf}
    (h : Sim (stageAt a t) φ') : ∃ t', φ' = stageAt a t' ∧ TEq t t' := by
  obtain ⟨w, rfl, hw⟩ := h
  refine ⟨w 0, rel_eq_vec _ w, ?_⟩
  rcases hw with hw | ⟨-, hw⟩
  · rw [← hw]; exact TEq.refl _
  · exact hw 0

theorem nstage_sim {a : Stage} {t : SyntacticTerm LIinf} {φ' : Proposition LIinf}
    (h : Sim (nstageAt a t) φ') : ∃ t', φ' = nstageAt a t' ∧ TEq t t' := by
  obtain ⟨w, rfl, hw⟩ := h
  refine ⟨w 0, nrel_eq_vec _ w, ?_⟩
  rcases hw with hw | ⟨-, hw⟩
  · rw [← hw]; exact TEq.refl _
  · exact hw 0

theorem X_sim {t : SyntacticTerm LIinf} {φ' : Proposition LIinf} (h : Sim (XinfAt t) φ') :
    φ' = XinfAt t := by
  obtain ⟨w, rfl, hw⟩ := h
  rcases hw with hw | ⟨hr, -⟩
  · rw [← hw]; rfl
  · exact absurd trivial hr

theorem nX_sim {t : SyntacticTerm LIinf} {φ' : Proposition LIinf}
    (h : Sim (∼(XinfAt t)) φ') : φ' = ∼(XinfAt t) := by
  obtain ⟨w, rfl, hw⟩ := h
  rcases hw with hw | ⟨hr, -⟩
  · rw [← hw]; rfl
  · exact absurd trivial hr

/-- The statement of term replacement for a derivation of `Δ`. -/
def ReplClaim (A : Semisentence LXI 1) (ρ : ThetaNote) (H : Set ThetaNote → Set ThetaNote)
    (α : ThetaNote) (Δ : Sequent LIinf) : Prop :=
  ThetaNote.IsOperator H → ∀ Γ' : Sequent LIinf, (∀ φ ∈ Δ, ∃ φ' ∈ Γ', Sim φ φ') →
    paramsList Γ' ⊆ H ∅ → IDerivable A ρ H α Γ'

theorem cover_cons {Δ Γ' : Sequent LIinf} {φ φ' : Proposition LIinf} (h : Sim φ φ')
    (hΔ : ∀ ψ ∈ Δ, ∃ ψ' ∈ Γ', Sim ψ ψ') : ∀ ψ ∈ φ :: Δ, ∃ ψ' ∈ φ' :: Γ', Sim ψ ψ' := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact ⟨φ', List.mem_cons_self, h⟩
  · obtain ⟨ψ', h1, h2⟩ := hΔ ψ hψ
    exact ⟨ψ', List.mem_cons_of_mem _ h1, h2⟩

theorem params_cons_sub {H : Set ThetaNote → Set ThetaNote} {Γ' : Sequent LIinf}
    {φ φ' : Proposition LIinf} (h : Sim φ φ') (hφ : params φ ⊆ H ∅) (hΓ : paramsList Γ' ⊆ H ∅) :
    paramsList (φ' :: Γ') ⊆ H ∅ := by
  rw [paramsList_cons, h.params_eq]
  exact Set.union_subset hφ hΓ

theorem replace_aux (hA : XFreeL A) {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote}
    {Δ : Sequent LIinf} (d : IDerivable A ρ H α Δ) : ReplClaim A ρ H α Δ := by
  induction d with
  | literal hα _ hφ hm =>
    intro _ Γ' hΔ hP
    obtain ⟨φ', h1, h2⟩ := hΔ _ hm
    exact .literal hα hP (h2.trueLit hφ) h1
  | verum hα _ hm =>
    intro _ Γ' hΔ hP
    obtain ⟨φ', h1, h2⟩ := hΔ _ hm
    obtain rfl : φ' = ⊤ := h2
    exact .verum hα hP h1
  | idX t hα _ hm1 hm2 =>
    intro _ Γ' hΔ hP
    obtain ⟨φ₁, h1, e1⟩ := hΔ _ hm1
    obtain ⟨φ₂, h2, e2⟩ := hΔ _ hm2
    rw [X_sim e1] at h1
    rw [nX_sim e2] at h2
    exact .idX t hα hP h1 h2
  | and hα _ hm h0 h1 d0 d1 ih0 ih1 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hs⟩ := hΔ _ hm
    obtain ⟨ψ₁, ψ₂, rfl, s₁, s₂⟩ := hs
    exact .and hα hP hχ h0 h1
      (ih0 hH _ (cover_cons s₁ hΔ) (params_cons_sub s₁ d0.params_head_subset hP))
      (ih1 hH _ (cover_cons s₂ hΔ) (params_cons_sub s₂ d1.params_head_subset hP))
  | orL hα _ hm h0 d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hs⟩ := hΔ _ hm
    obtain ⟨ψ₁, ψ₂, rfl, s₁, -⟩ := hs
    exact .orL hα hP hχ h0
      (ih0 hH _ (cover_cons s₁ hΔ) (params_cons_sub s₁ d0.params_head_subset hP))
  | orR hα _ hm h1 h0 d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hs⟩ := hΔ _ hm
    obtain ⟨ψ₁, ψ₂, rfl, -, s₂⟩ := hs
    exact .orR hα hP hχ h1 h0
      (ih0 hH _ (cover_cons s₂ hΔ) (params_cons_sub s₂ d0.params_head_subset hP))
  | all f hα _ hm hf d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hs⟩ := hΔ _ hm
    obtain ⟨ψ', rfl, s'⟩ := hs
    exact .all f hα hP hχ hf fun n =>
      ih0 n hH _ (cover_cons (s'.subst_numI n) hΔ)
        (params_cons_sub (s'.subst_numI n) (d0 n).params_head_subset hP)
  | exs n hα _ hm hn h0 d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hs⟩ := hΔ _ hm
    obtain ⟨ψ', rfl, s'⟩ := hs
    exact .exs n hα hP hχ hn h0
      (ih0 hH _ (cover_cons (s'.subst_numI n) hΔ)
        (params_cons_sub (s'.subst_numI n) d0.params_head_subset hP))
  | stage g hα _ hm hga hgα hgH h0 d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hs⟩ := hΔ _ hm
    obtain ⟨t', rfl, ht⟩ := stage_sim hs
    have s' := sim_unfold hA g ht
    exact .stage g hα hP hχ hga hgα hgH h0
      (ih0 hH _ (cover_cons s' hΔ) (params_cons_sub s' d0.params_head_subset hP))
  | @nstage H' α' Δ' a t f hα _ hm hf d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hs⟩ := hΔ _ hm
    obtain ⟨t', rfl, ht⟩ := nstage_sim hs
    refine .nstage f hα hP hχ hf fun g hg => ?_
    have s' := (sim_unfold hA g ht).neg
    have hsub : H' ∅ ⊆ ThetaNote.adjoin H' {g.1} ∅ := hH.mono (Set.empty_subset _)
    exact ih0 g hg (hH.adjoin {g.1}) _ (cover_cons s' hΔ)
      (params_cons_sub s' (d0 g hg).params_head_subset (hP.trans hsub))
  | fix hα _ hm hΩ h0 d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hs⟩ := hΔ _ hm
    obtain ⟨t', rfl, ht⟩ := stage_sim hs
    have s' := sim_unfold hA Stage.top ht
    exact .fix hα hP hχ hΩ h0
      (ih0 hH _ (cover_cons s' hΔ) (params_cons_sub s' d0.params_head_subset hP))
  | cut hα _ hr h0 d0 d1 ih0 ih1 =>
    intro hH Γ' hΔ hP
    exact .cut hα hP hr h0
      (ih0 hH _ (cover_cons (Sim.refl _) hΔ)
        (params_cons_sub (Sim.refl _) d0.params_head_subset hP))
      (ih1 hH _ (cover_cons (Sim.refl _) hΔ)
        (params_cons_sub (Sim.refl _) d1.params_head_subset hP))

/-- **Term replacement** (Freund, proof of Proposition 6.4): if every formula of `Γ` is
`Sim`-related to a formula of `Γ'`, then `H ⊢^α_ρ Γ` gives `H ⊢^α_ρ Γ'`. -/
theorem IDerivable.replace (hA : XFreeL A) {H : Set ThetaNote → Set ThetaNote}
    (hH : ThetaNote.IsOperator H) {α : ThetaNote} {Γ Γ' : Sequent LIinf}
    (d : IDerivable A ρ H α Γ) (hΓ : ∀ φ ∈ Γ, ∃ φ' ∈ Γ', Sim φ φ')
    (hP : paramsList Γ' ⊆ H ∅) : IDerivable A ρ H α Γ' :=
  replace_aux hA d hH Γ' hΓ hP

/-- Term replacement in the head formula. -/
theorem IDerivable.replace_head (hA : XFreeL A) {H : Set ThetaNote → Set ThetaNote}
    (hH : ThetaNote.IsOperator H) {α : ThetaNote} {Γ : Sequent LIinf} {φ φ' : Proposition LIinf}
    (d : IDerivable A ρ H α (φ :: Γ)) (h : Sim φ φ') : IDerivable A ρ H α (φ' :: Γ) := by
  refine d.replace hA hH (cover_cons h fun ψ hψ => ⟨ψ, hψ, Sim.refl ψ⟩) ?_
  have hP := d.params_subset
  rw [paramsList_cons] at hP ⊢
  rw [h.params_eq]
  exact hP

end Replace

end InductiveDef

end OrdinalAnalysis
