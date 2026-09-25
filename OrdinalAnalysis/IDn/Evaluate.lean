/-
  Closed terms and their values in the infinitary calculus of `ID_{<ω}`, `n` simultaneous
  inductive definitions with stage predicates `I_k^{≺α}`, `k : Fin n`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §6: the remark in the proof of Proposition 6.4
  ("we can replace any occurrence of `t` by the numeral with the same value, since the
  notion of false literal in Definition 5.1 is unaffected"), used again for the
  existential quantifier in the proof of Theorem 6.5; after Exercise 3.5 of the first
  lecture. As ported by `ID1/Evaluate.lean`, generalised to `n` levels.

  **No evaluator.**  The calculus instantiates a quantifier `∀x ψ(x)` at the numerals
  `ψ(m̄)`, not at evaluated instances, so no normalisation of closed terms is built into
  it.  What the embedding needs instead is Freund's remark: a derivation of `Γ` stays a
  derivation, at the same height, cut rank and operator, when closed terms are replaced
  by closed terms of the same value.  The rules that inspect a closed term only through
  its value are the arithmetic literals (Definition 5.1: a literal is true or false by
  the value of its arguments); the stage rules and (Fix) at every level carry the term
  into the premise `A_k(t, I_k^{≺γ})` unchanged, and the quantifier rules substitute
  numerals, which commutes with the replacement.

  One rule of the calculus as built is *not* blind to terms: the identity clause `idX` for
  the free predicate `X` asks for literally the same term in `X t` and `¬X t`, and
  Freund's language has no `X`.  So the replacement is allowed at arithmetic and stage
  literals only; a literal `X t` must stay as it is (`RelOK`).  The operator forms `A k`
  are then required to be `X`-free (`XFreeL (A k)`, every level), since the stage rules
  move the term into `A_k(t, I_k^{≺γ})`.

  **The relation.**  `TEq s t`: `s = t`, or both are free of free variables and have the
  same value under every assignment.  `Sim φ ψ`: `ψ` is `φ` with some arguments of
  arithmetic and stage literals replaced by `TEq`-related terms.  Then

      H ⊢^α_ρ Γ,  every formula of Γ is Sim-related to a formula of Γ'
        ⇒  H ⊢^α_ρ Γ'                                       (`IDnDerivable.replace`),

  which also contains weakening in the sequent.

  **`IsXRelN`/`XFreeI`/`XFreeL`/`xFreeI_rew`/`numeral_freeVariables`/`numI_freeVariables`
  are also used, verbatim, by `IDn/NumSubst.lean`** (currently a temporary local copy there,
  pending this file — see that file's docstring); kept syntactically identical to `ID1`'s so
  that copy can simply be deleted in favour of importing this one.

  Contents.

    `lMap_toLIinfN_numeral`, `val_numI`      a numeral denotes its value
    `closedVal`, `val_closed`                the value of a closed term
    `ThetaWNoteD.le_omegaMul`                `α ⪯ ω · α` (by well-foundedness)
    `IsXRelN`, `XFreeI`, `XFreeL`            formulas without the free predicate `X`
    `TEq`, `RelOK`, `Sim`                    the replacement relation
    `Sim.refl`, `Sim.neg`, `Sim.params_eq`, `Sim.rew`, `Sim.trueLit`
    `Sim.of_rew_pair`                        two closed instances of the same formula
    `sim_subst_closed`, `sim_subst_numI`     `ψ(s) ~ ψ(t)` for closed `s`, `t` of equal value
    `IDnDerivable.replace`, `replace_head`   **term replacement**
-/
import OrdinalAnalysis.IDn.Calculus

set_option autoImplicit false

namespace OrdinalAnalysis

variable {n : ℕ}

/-! ### Numerals denote their values -/

namespace IDn

open LO LO.FirstOrder

section Numeral

variable {ξ : Type*} {m : ℕ}

private lemma lMapNumI_zero :
    Semiterm.lMap (toLIinfN n) ((0 : ℕ) : Semiterm ℒₒᵣ ξ m) =
      ((0 : ℕ) : Semiterm (LIinfN n) ξ m) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, toLIinfN]

private lemma lMapNumI_one :
    Semiterm.lMap (toLIinfN n) ((1 : ℕ) : Semiterm ℒₒᵣ ξ m) =
      ((1 : ℕ) : Semiterm (LIinfN n) ξ m) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, toLIinfN]

private lemma lMapNumI_add (v : Fin 2 → Semiterm ℒₒᵣ ξ m) :
    Semiterm.lMap (toLIinfN n) (Semiterm.Operator.Add.add.operator v) =
      Semiterm.Operator.Add.add.operator (Semiterm.lMap (toLIinfN n) ∘ v) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, toLIinfN]
  funext i
  simp

private lemma numeralI_succ_succ (L : Language) [L.Zero] [L.One] [L.Add] (t : ℕ) :
    ((t + 1 + 1 : ℕ) : Semiterm L ξ m) =
      Semiterm.Operator.Add.add.operator
        ![((t + 1 : ℕ) : Semiterm L ξ m), ((1 : ℕ) : Semiterm L ξ m)] := by
  have h : t + 1 ≠ 0 := Nat.succ_ne_zero t
  simp only [Semiterm.numeral, Semiterm.Operator.const,
    Semiterm.Operator.numeral_succ h, Semiterm.Operator.operator_comp]
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- The numerals of `LIinfN n` are the numerals of arithmetic. -/
theorem lMap_toLIinfN_numeral (t : ℕ) :
    Semiterm.lMap (toLIinfN n) ((t : ℕ) : Semiterm ℒₒᵣ ξ m) =
      ((t : ℕ) : Semiterm (LIinfN n) ξ m) := by
  induction t with
  | zero => exact lMapNumI_zero
  | succ t ih =>
    cases t with
    | zero => exact lMapNumI_one
    | succ t =>
      rw [numeralI_succ_succ ℒₒᵣ t, numeralI_succ_succ (LIinfN n) t, lMapNumI_add]
      congr 1
      funext i
      match i with
      | ⟨0, _⟩ => exact ih
      | ⟨1, _⟩ => exact lMapNumI_one

/-- **A numeral denotes its value** in the standard structure. -/
@[simp] theorem val_numeral_stdInfN (p : ℕ) (e : Fin m → ℕ) (ε : ξ → ℕ) :
    Semiterm.val (s := stdInfN) e ε ((p : ℕ) : Semiterm (LIinfN n) ξ m) = p := by
  rw [← lMap_toLIinfN_numeral p]
  show Semiterm.val (s := Structure.add ℒₒᵣ (IInfLangN n) ℕ (str₂ := iinfFalseN)) e ε
    (Semiterm.lMap (Language.Hom.add₁ ℒₒᵣ (IInfLangN n)) ((p : ℕ) : Semiterm ℒₒᵣ ξ m)) = p
  rw [Structure.val_lMap_add₁ (str₂ := iinfFalseN)]
  simp

@[simp] theorem val_numI (p : ℕ) (e : Fin 0 → ℕ) (ε : ℕ → ℕ) :
    Semiterm.val (s := stdInfN) e ε (numI (n := n) p) = p :=
  val_numeral_stdInfN p e ε

end Numeral

/-! ### Formulas without `X`

`IsXRelN`/`XFreeI`/`XFreeL`/`xFreeI_rew` here are the definitions `IDn/NumSubst.lean` currently
keeps as a temporary local copy (its docstring says so); the two must stay syntactically
identical, since `IDn/NumSubst.lean`'s copy is to be deleted in favour of importing this file. -/

section XFree

variable {ξ : Type*}

/-- `r` is the free predicate `X`. -/
def IsXRelN : {k : ℕ} → (LIinfN n).Rel k → Prop
  | _, Sum.inl _ => False
  | _, Sum.inr IInfRelN.X => True
  | _, Sum.inr (IInfRelN.stage _) => False

/-- A formula of `LIinfN n` without the free predicate `X`. -/
def XFreeI : {m : ℕ} → Semiformula (LIinfN n) ξ m → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel r _ => ¬IsXRelN r
  | _, .nrel r _ => ¬IsXRelN r
  | _, .and φ ψ => XFreeI φ ∧ XFreeI ψ
  | _, .or φ ψ => XFreeI φ ∧ XFreeI ψ
  | _, .all φ => XFreeI φ
  | _, .exs φ => XFreeI φ

/-- A formula of `LXIn n` without the free predicate `X`. -/
def XFreeL : {m : ℕ} → Semiformula (LXIn n) ξ m → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel (Sum.inl _) _ => True
  | _, .rel (Sum.inr IXRelN.X) _ => False
  | _, .rel (Sum.inr (IXRelN.I _)) _ => True
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr IXRelN.X) _ => False
  | _, .nrel (Sum.inr (IXRelN.I _)) _ => True
  | _, .and φ ψ => XFreeL φ ∧ XFreeL ψ
  | _, .or φ ψ => XFreeL φ ∧ XFreeL ψ
  | _, .all φ => XFreeL φ
  | _, .exs φ => XFreeL φ

@[simp] theorem xFreeI_neg {m : ℕ} (φ : Semiformula (LIinfN n) ξ m) : XFreeI (∼φ) ↔ XFreeI φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v => exact Iff.rfl
  | hnrel r v => exact Iff.rfl
  | hand φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | hor φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | hall φ ih => exact ih
  | hexs φ ih => exact ih

@[simp] theorem xFreeI_rew {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfN n) ξ₁ m₁ ξ₂ m₂)
    (φ : Semiformula (LIinfN n) ξ₁ m₁) : XFreeI (ω ▹ φ) ↔ XFreeI φ := by
  induction φ using Semiformula.rec' generalizing m₂ with
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

theorem isXRelN_stageRel_I (k : Fin n) (a : StageAt k.val) (j : Fin n) :
    ¬IsXRelN (stageRel k a (Sum.inr (IXRelN.I j))) := by
  rw [stageRel_I]; split <;> exact fun h => h

theorem xFreeI_lMap_stageHom (k : Fin n) (a : StageAt k.val) {m : ℕ} :
    ∀ (φ : Semiformula (LXIn n) ξ m), XFreeL φ → XFreeI (Semiformula.lMap (stageHom k a) φ)
  | .verum, _ => trivial
  | .falsum, _ => trivial
  | .rel (Sum.inl _) _, _ => fun h => h
  | .rel (Sum.inr IXRelN.X) _, h => h.elim
  | .rel (Sum.inr (IXRelN.I j)) _, _ => isXRelN_stageRel_I k a j
  | .nrel (Sum.inl _) _, _ => fun h => h
  | .nrel (Sum.inr IXRelN.X) _, h => h.elim
  | .nrel (Sum.inr (IXRelN.I j)) _, _ => isXRelN_stageRel_I k a j
  | .and φ ψ, h => ⟨xFreeI_lMap_stageHom k a φ h.1, xFreeI_lMap_stageHom k a ψ h.2⟩
  | .or φ ψ, h => ⟨xFreeI_lMap_stageHom k a φ h.1, xFreeI_lMap_stageHom k a ψ h.2⟩
  | .all φ, h => xFreeI_lMap_stageHom k a φ h
  | .exs φ, h => xFreeI_lMap_stageHom k a φ h

/-- For an `X`-free operator form, every unfolding is `X`-free. -/
theorem xFreeI_unfold_body {A : Semisentence (LXIn n) 1} (hA : XFreeL A) (k : Fin n)
    (a : StageAt k.val) : XFreeI (Rew.emb ▹ formAt A k a : Semiformula (LIinfN n) ℕ 1) :=
  (xFreeI_rew _ _).mpr (xFreeI_lMap_stageHom k a A hA)

end XFree

/-! ### Numerals have no free variable

`numeral_freeVariables`/`numI_freeVariables` here are also `IDn/NumSubst.lean`'s temporary local
copy; kept syntactically identical for the same reason as the `XFree` section above. -/

section NumeralFreeVariables

/-- A numeral at any level has no free variable. -/
theorem numeral_freeVariables (p : ℕ) {m : ℕ} :
    ((p : ℕ) : Semiterm (LIinfN n) ℕ m).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hx' : ((Rew.subst ![]) (Rew.emb (Semiterm.Operator.numeral (LIinfN n) p).term) :
      Semiterm (LIinfN n) ℕ m).FVar? x := hx
  rcases Semiterm.fvar?_rew hx' with ⟨i, -⟩ | ⟨z, hz, -⟩
  · exact i.elim0
  · have hz' : z ∈ (Rew.emb (Semiterm.Operator.numeral (LIinfN n) p).term :
        Semiterm (LIinfN n) ℕ 0).freeVariables := hz
    simp at hz'

theorem numI_freeVariables (p : ℕ) : (numI (n := n) p).freeVariables = ∅ :=
  numeral_freeVariables p

end NumeralFreeVariables

/-- Every rewriting fixes a numeral. -/
@[simp] theorem rew_numeral {ξ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfN n) ξ m₁ ξ m₂) (p : ℕ) :
    ω ((p : ℕ) : Semiterm (LIinfN n) ξ m₁) = ((p : ℕ) : Semiterm (LIinfN n) ξ m₂) := by
  simp

/-! ### The value of a closed term -/

/-- The value of a closed term in the standard structure. -/
def closedVal (t : SyntacticTerm (LIinfN n)) : ℕ :=
  Semiterm.val (s := stdInfN) ![] (fun _ => 0) t

/-- The value of a term without free variables does not depend on the assignment. -/
theorem val_closed {t : SyntacticTerm (LIinfN n)} (ht : t.freeVariables = ∅) (e : Fin 0 → ℕ)
    (ε : ℕ → ℕ) : Semiterm.val (s := stdInfN) e ε t = closedVal t := by
  unfold closedVal
  have he : e = ![] := funext fun i => i.elim0
  subst he
  refine Semiterm.val_eq_of_funEqOn t ?_
  intro x hx
  have hx' : x ∈ t.freeVariables := hx
  rw [ht] at hx'
  exact absurd hx' (Finset.notMem_empty x)

@[simp] theorem closedVal_numI (p : ℕ) : closedVal (numI (n := n) p) = p := val_numI p ![] _

end IDn

/-! ### `α ⪯ ω · α` -/

namespace ThetaWNoteD

/-- **`α ⪯ ω · α`**: a strictly increasing map of a well-order is inflationary. -/
theorem le_omegaMul (a : ThetaWNoteD) : a ≤ ThetaWNoteD.omegaMul a := by
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    by_contra h
    have hlt : ThetaWNoteD.omegaMul a < a := lt_of_not_ge h
    have h1 := ih _ hlt
    exact absurd (ThetaWNoteD.omegaMul_lt_omegaMul hlt) (not_lt_of_ge h1)

end ThetaWNoteD

namespace IDn

open LO LO.FirstOrder

/-! ### The replacement relation -/

section Sim

variable {ξ : Type*} {m : ℕ}

/-- `s` and `t` are equal, or both are free of free variables and have the same value under
every assignment. -/
def TEq {m : ℕ} (s t : Semiterm (LIinfN n) ℕ m) : Prop :=
  s = t ∨ (s.freeVariables = ∅ ∧ t.freeVariables = ∅ ∧
    ∀ (e : Fin m → ℕ) (ε : ℕ → ℕ),
      Semiterm.val (s := stdInfN) e ε s = Semiterm.val (s := stdInfN) e ε t)

/-- The arguments of a literal may be replaced, unless the literal is an `X`-literal. -/
def RelOK {m k : ℕ} (r : (LIinfN n).Rel k) (v w : Fin k → Semiterm (LIinfN n) ℕ m) : Prop :=
  v = w ∨ (¬IsXRelN r ∧ ∀ i, TEq (v i) (w i))

/-- **`Sim φ ψ`**: `ψ` is `φ` with some arguments of arithmetic and stage literals replaced by
`TEq`-related terms. -/
def Sim : {m : ℕ} → Semiformula (LIinfN n) ℕ m → Semiformula (LIinfN n) ℕ m → Prop
  | _, .verum, ψ => ψ = ⊤
  | _, .falsum, ψ => ψ = ⊥
  | _, .rel r v, ψ => ∃ w, ψ = .rel r w ∧ RelOK r v w
  | _, .nrel r v, ψ => ∃ w, ψ = .nrel r w ∧ RelOK r v w
  | _, .and φ₁ φ₂, ψ => ∃ ψ₁ ψ₂, ψ = ψ₁ ⋏ ψ₂ ∧ Sim φ₁ ψ₁ ∧ Sim φ₂ ψ₂
  | _, .or φ₁ φ₂, ψ => ∃ ψ₁ ψ₂, ψ = ψ₁ ⋎ ψ₂ ∧ Sim φ₁ ψ₁ ∧ Sim φ₂ ψ₂
  | _, .all φ, ψ => ∃ ψ', ψ = ∀¹ ψ' ∧ Sim φ ψ'
  | _, .exs φ, ψ => ∃ ψ', ψ = ∃¹ ψ' ∧ Sim φ ψ'

theorem TEq.refl {m : ℕ} (t : Semiterm (LIinfN n) ℕ m) : TEq t t := Or.inl rfl

theorem RelOK.refl {m k : ℕ} (r : (LIinfN n).Rel k) (v : Fin k → Semiterm (LIinfN n) ℕ m) :
    RelOK r v v := Or.inl rfl

theorem Sim.refl {m : ℕ} (φ : Semiformula (LIinfN n) ℕ m) : Sim φ φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact rfl
  | hfalsum => exact rfl
  | hrel r v => exact ⟨v, rfl, RelOK.refl r v⟩
  | hnrel r v => exact ⟨v, rfl, RelOK.refl r v⟩
  | hand φ ψ ihφ ihψ => exact ⟨φ, ψ, rfl, ihφ, ihψ⟩
  | hor φ ψ ihφ ihψ => exact ⟨φ, ψ, rfl, ihφ, ihψ⟩
  | hall φ ih => exact ⟨φ, rfl, ih⟩
  | hexs φ ih => exact ⟨φ, rfl, ih⟩

theorem Sim.neg {m : ℕ} {φ ψ : Semiformula (LIinfN n) ℕ m} (h : Sim φ ψ) : Sim (∼φ) (∼ψ) := by
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
theorem Sim.params_eq {m : ℕ} {φ ψ : Semiformula (LIinfN n) ℕ m} (h : Sim φ ψ) :
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
theorem freeVariables_rew_term {m₁ m₂ : ℕ} (ω : Rew (LIinfN n) ℕ m₁ ℕ m₂)
    (hb : ∀ x, (ω #x).freeVariables = ∅) :
    ∀ {t : Semiterm (LIinfN n) ℕ m₁}, t.freeVariables = ∅ → (ω t).freeVariables = ∅ := by
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

theorem freeVariables_bShift {m : ℕ} (t : Semiterm (LIinfN n) ℕ m) :
    (Rew.bShift t).freeVariables = t.freeVariables := by
  ext x
  exact Semiterm.fvar?_bShift

/-- The rewritings that keep `Sim`: the bound variables go to terms without free
variables. -/
def BClosed {m₁ m₂ : ℕ} (ω : Rew (LIinfN n) ℕ m₁ ℕ m₂) : Prop :=
  ∀ x, (ω #x).freeVariables = ∅

theorem BClosed.q {m₁ m₂ : ℕ} {ω : Rew (LIinfN n) ℕ m₁ ℕ m₂} (h : BClosed ω) : BClosed ω.q := by
  intro x
  cases x using Fin.cases with
  | zero => rw [Rew.q_bvar_zero]; rfl
  | succ x => rw [Rew.q_bvar_succ, freeVariables_bShift]; exact h x

theorem TEq.rew {m₁ m₂ : ℕ} {ω : Rew (LIinfN n) ℕ m₁ ℕ m₂} (hω : BClosed ω)
    {s t : Semiterm (LIinfN n) ℕ m₁} (h : TEq s t) : TEq (ω s) (ω t) := by
  rcases h with rfl | ⟨hs, ht, hv⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨freeVariables_rew_term ω hω hs, freeVariables_rew_term ω hω ht, ?_⟩
    intro e ε
    rw [Semiterm.val_rew, Semiterm.val_rew]
    exact hv _ _

theorem RelOK.rew {m₁ m₂ k : ℕ} {ω : Rew (LIinfN n) ℕ m₁ ℕ m₂} (hω : BClosed ω)
    {r : (LIinfN n).Rel k} {v w : Fin k → Semiterm (LIinfN n) ℕ m₁} (h : RelOK r v w) :
    RelOK r (ω ∘ v) (ω ∘ w) := by
  rcases h with rfl | ⟨hr, h⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hr, fun i => (h i).rew hω⟩

/-- **`Sim` is stable under rewritings whose bound-variable images have no free variables**,
in particular under the instantiation of a quantifier at a numeral. -/
theorem Sim.rew {m₁ : ℕ} {φ ψ : Semiformula (LIinfN n) ℕ m₁} (h : Sim φ ψ) :
    ∀ {m₂ : ℕ} {ω : Rew (LIinfN n) ℕ m₁ ℕ m₂}, BClosed ω → Sim (ω ▹ φ) (ω ▹ ψ) := by
  induction φ using Semiformula.rec' with
  | hverum =>
    intro m₂ ω _; obtain rfl : ψ = ⊤ := h
    simp only [LogicalConnective.HomClass.map_top]; exact rfl
  | hfalsum =>
    intro m₂ ω _; obtain rfl : ψ = ⊥ := h
    simp only [LogicalConnective.HomClass.map_bot]; exact rfl
  | hrel r v =>
    intro m₂ ω hω
    obtain ⟨w, rfl, hw⟩ := h
    rw [Semiformula.rew_rel, Semiformula.rew_rel]
    exact ⟨_, rfl, hw.rew hω⟩
  | hnrel r v =>
    intro m₂ ω hω
    obtain ⟨w, rfl, hw⟩ := h
    rw [Semiformula.rew_nrel, Semiformula.rew_nrel]
    exact ⟨_, rfl, hw.rew hω⟩
  | hand φ₁ φ₂ ih₁ ih₂ =>
    intro m₂ ω hω
    obtain ⟨ψ₁, ψ₂, rfl, h₁, h₂⟩ := h
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact ⟨_, _, rfl, ih₁ h₁ hω, ih₂ h₂ hω⟩
  | hor φ₁ φ₂ ih₁ ih₂ =>
    intro m₂ ω hω
    obtain ⟨ψ₁, ψ₂, rfl, h₁, h₂⟩ := h
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact ⟨_, _, rfl, ih₁ h₁ hω, ih₂ h₂ hω⟩
  | hall φ ih =>
    intro m₂ ω hω
    obtain ⟨ψ', rfl, h'⟩ := h
    rw [Rewriting.app_all, Rewriting.app_all]
    exact ⟨_, rfl, ih h' hω.q⟩
  | hexs φ ih =>
    intro m₂ ω hω
    obtain ⟨ψ', rfl, h'⟩ := h
    rw [Rewriting.app_exs, Rewriting.app_exs]
    exact ⟨_, rfl, ih h' hω.q⟩

theorem bClosed_subst_numI (p : ℕ) :
    BClosed (Rew.subst ![numI p] : Rew (LIinfN n) ℕ 1 ℕ 0) := by
  intro x
  cases x using Fin.cases with
  | zero => simpa using numI_freeVariables p
  | succ x => exact x.elim0

theorem Sim.subst_numI {φ ψ : Semiformula (LIinfN n) ℕ 1} (h : Sim φ ψ) (p : ℕ) :
    Sim (φ/[numI p]) (ψ/[numI p]) :=
  h.rew (bClosed_subst_numI p)

/-- **The truth of an arithmetic literal sees only the values of its arguments.** -/
theorem Sim.trueLit {φ ψ : Proposition (LIinfN n)} (h : Sim φ ψ) (hφ : TrueLit φ) : TrueLit ψ := by
  obtain ⟨⟨j, r, v, hform, hv⟩, htrue⟩ := hφ
  have key : ∀ w : Fin j → SyntacticTerm (LIinfN n), RelOK (Sum.inl r : (LIinfN n).Rel j) v w →
      (∀ i, (w i).freeVariables = ∅) ∧
        (fun i => Semiterm.val (s := stdInfN) ![] (fun _ => 0) (v i)) =
          (fun i => Semiterm.val (s := stdInfN) ![] (fun _ => 0) (w i)) := by
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
    refine ⟨⟨j, r, w, Or.inl rfl, hw'⟩, ?_⟩
    have ht : Semiformula.Eval (s := stdInfN) ![] (fun _ => 0)
        (Semiformula.rel (Sum.inl r : (LIinfN n).Rel j) v) := htrue
    have hval' : (Semiterm.val (s := stdInfN) ![] (fun _ => 0) ∘ v) =
        (Semiterm.val (s := stdInfN) ![] (fun _ => 0) ∘ w) := hval
    exact (Semiformula.eval_rel (s := stdInfN) (r := (Sum.inl r : (LIinfN n).Rel j))).mpr
      (hval' ▸ (Semiformula.eval_rel (s := stdInfN) (r := (Sum.inl r : (LIinfN n).Rel j))).mp ht)
  · obtain ⟨w, rfl, hw⟩ := h
    obtain ⟨hw', hval⟩ := key w hw
    refine ⟨⟨j, r, w, Or.inr rfl, hw'⟩, ?_⟩
    have ht : Semiformula.Eval (s := stdInfN) ![] (fun _ => 0)
        (Semiformula.nrel (Sum.inl r : (LIinfN n).Rel j) v) := htrue
    have hval' : (Semiterm.val (s := stdInfN) ![] (fun _ => 0) ∘ v) =
        (Semiterm.val (s := stdInfN) ![] (fun _ => 0) ∘ w) := hval
    exact (Semiformula.eval_nrel (s := stdInfN) (r := (Sum.inl r : (LIinfN n).Rel j))).mpr
      (hval' ▸ (Semiformula.eval_nrel (s := stdInfN) (r := (Sum.inl r : (LIinfN n).Rel j))).mp ht)

/-- Two rewritings that send the bound variables to terms without free variables of equal
values, and agree on the free variables. -/
def PairOK {m₁ m₂ : ℕ} (ω ω' : Rew (LIinfN n) ℕ m₁ ℕ m₂) : Prop :=
  (∀ x, (ω #x).freeVariables = ∅ ∧ (ω' #x).freeVariables = ∅ ∧
    ∀ (e : Fin m₂ → ℕ) (ε : ℕ → ℕ),
      Semiterm.val (s := stdInfN) e ε (ω #x) = Semiterm.val (s := stdInfN) e ε (ω' #x)) ∧
  ∀ x, ω &x = ω' &x

theorem PairOK.q {m₁ m₂ : ℕ} {ω ω' : Rew (LIinfN n) ℕ m₁ ℕ m₂} (h : PairOK ω ω') :
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

theorem PairOK.teq {m₁ m₂ : ℕ} {ω ω' : Rew (LIinfN n) ℕ m₁ ℕ m₂} (h : PairOK ω ω')
    {t : Semiterm (LIinfN n) ℕ m₁} (ht : t.freeVariables = ∅) : TEq (ω t) (ω' t) := by
  refine Or.inr ⟨freeVariables_rew_term ω (fun x => (h.1 x).1) ht,
    freeVariables_rew_term ω' (fun x => (h.1 x).2.1) ht, fun e ε => ?_⟩
  rw [Semiterm.val_rew, Semiterm.val_rew]
  congr 1
  · funext x; exact (h.1 x).2.2 e ε
  · funext x; simp only [Function.comp_apply, h.2 x]

theorem freeVariables_rel_arg {m k : ℕ} {r : (LIinfN n).Rel k}
    {v : Fin k → Semiterm (LIinfN n) ℕ m} (h : (Semiformula.rel r v).freeVariables = ∅)
    (i : Fin k) : (v i).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have : x ∈ (Semiformula.rel r v).freeVariables := by
    rw [Semiformula.freeVariables_rel]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  rw [h] at this
  exact Finset.notMem_empty x this

theorem freeVariables_nrel_arg {m k : ℕ} {r : (LIinfN n).Rel k}
    {v : Fin k → Semiterm (LIinfN n) ℕ m} (h : (Semiformula.nrel r v).freeVariables = ∅)
    (i : Fin k) : (v i).freeVariables = ∅ := by
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
theorem Sim.of_rew_pair {m₁ : ℕ} {φ : Semiformula (LIinfN n) ℕ m₁} (hφ : φ.freeVariables = ∅)
    (hX : XFreeI φ) :
    ∀ {m₂ : ℕ} {ω ω' : Rew (LIinfN n) ℕ m₁ ℕ m₂}, PairOK ω ω' → Sim (ω ▹ φ) (ω' ▹ φ) := by
  induction φ using Semiformula.rec' with
  | hverum =>
    intro m₂ ω ω' _
    simp only [LogicalConnective.HomClass.map_top]; exact rfl
  | hfalsum =>
    intro m₂ ω ω' _
    simp only [LogicalConnective.HomClass.map_bot]; exact rfl
  | hrel r v =>
    intro m₂ ω ω' h
    rw [Semiformula.rew_rel, Semiformula.rew_rel]
    exact ⟨_, rfl, Or.inr ⟨hX, fun i => h.teq (freeVariables_rel_arg hφ i)⟩⟩
  | hnrel r v =>
    intro m₂ ω ω' h
    rw [Semiformula.rew_nrel, Semiformula.rew_nrel]
    exact ⟨_, rfl, Or.inr ⟨hX, fun i => h.teq (freeVariables_nrel_arg hφ i)⟩⟩
  | hand φ₁ φ₂ ih₁ ih₂ =>
    intro m₂ ω ω' h
    rw [Semiformula.freeVariables_and, Finset.union_eq_empty] at hφ
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact ⟨_, _, rfl, ih₁ hφ.1 hX.1 h, ih₂ hφ.2 hX.2 h⟩
  | hor φ₁ φ₂ ih₁ ih₂ =>
    intro m₂ ω ω' h
    rw [Semiformula.freeVariables_or, Finset.union_eq_empty] at hφ
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact ⟨_, _, rfl, ih₁ hφ.1 hX.1 h, ih₂ hφ.2 hX.2 h⟩
  | hall φ ih =>
    intro m₂ ω ω' h
    rw [Rewriting.app_all, Rewriting.app_all]
    exact ⟨_, rfl, ih hφ hX h.q⟩
  | hexs φ ih =>
    intro m₂ ω ω' h
    rw [Rewriting.app_exs, Rewriting.app_exs]
    exact ⟨_, rfl, ih hφ hX h.q⟩

/-- **`ψ(s) ~ ψ(t)`** for an `X`-free `ψ` without free variables and closed `s`, `t` of equal
value. -/
theorem sim_subst_closed {m : ℕ} {φ : Semiformula (LIinfN n) ℕ 1} (hφ : φ.freeVariables = ∅)
    (hX : XFreeI φ) {s t : Semiterm (LIinfN n) ℕ m} (hs : s.freeVariables = ∅)
    (ht : t.freeVariables = ∅)
    (hv : ∀ (e : Fin m → ℕ) (ε : ℕ → ℕ),
      Semiterm.val (s := stdInfN) e ε s = Semiterm.val (s := stdInfN) e ε t) :
    Sim (Rew.subst ![s] ▹ φ) (Rew.subst ![t] ▹ φ) := by
  refine Sim.of_rew_pair hφ hX ⟨fun x => ?_, fun x => ?_⟩
  · cases x using Fin.cases with
    | zero => simpa using ⟨hs, ht, hv⟩
    | succ x => exact x.elim0
  · simp

/-- **Freund's remark**: a closed term may be replaced by the numeral of its value. -/
theorem sim_subst_numI {φ : Semiformula (LIinfN n) ℕ 1} (hφ : φ.freeVariables = ∅) (hX : XFreeI φ)
    {t : SyntacticTerm (LIinfN n)} (ht : t.freeVariables = ∅) :
    Sim (φ/[t]) (φ/[numI (closedVal t)]) :=
  sim_subst_closed hφ hX ht (numI_freeVariables _) (fun e ε => by
    rw [val_closed ht, val_numI])

theorem TEq.sim_subst {φ : Semiformula (LIinfN n) ℕ 1} (hφ : φ.freeVariables = ∅) (hX : XFreeI φ)
    {t t' : SyntacticTerm (LIinfN n)} (h : TEq t t') : Sim (φ/[t]) (φ/[t']) := by
  rcases h with rfl | ⟨hs, ht, hv⟩
  · exact Sim.refl _
  · exact sim_subst_closed hφ hX hs ht hv

end Sim

/-! ### Term replacement -/

section Replace

variable {A : Fin n → Semisentence (LXIn n) 1} {ρ : ThetaWNoteD}

/-- The unfolding at two `TEq`-related terms. -/
theorem sim_unfold {k : Fin n} (hA : XFreeL (A k)) (g : StageAt k.val)
    {t t' : SyntacticTerm (LIinfN n)} (h : TEq t t') :
    Sim (unfold (A k) k g t) (unfold (A k) k g t') :=
  h.sim_subst (Semiformula.freeVariables_emb _) (xFreeI_unfold_body hA k g)

theorem stage_sim {s : Stage n} {t : SyntacticTerm (LIinfN n)} {φ' : Proposition (LIinfN n)}
    (h : Sim (stageAt s t) φ') : ∃ t', φ' = stageAt s t' ∧ TEq t t' := by
  obtain ⟨w, rfl, hw⟩ := h
  refine ⟨w 0, rel_eq_vec _ w, ?_⟩
  rcases hw with hw | ⟨-, hw⟩
  · rw [← hw]; exact TEq.refl _
  · exact hw 0

theorem nstage_sim {s : Stage n} {t : SyntacticTerm (LIinfN n)} {φ' : Proposition (LIinfN n)}
    (h : Sim (nstageAt s t) φ') : ∃ t', φ' = nstageAt s t' ∧ TEq t t' := by
  obtain ⟨w, rfl, hw⟩ := h
  refine ⟨w 0, nrel_eq_vec _ w, ?_⟩
  rcases hw with hw | ⟨-, hw⟩
  · rw [← hw]; exact TEq.refl _
  · exact hw 0

theorem X_sim {t : SyntacticTerm (LIinfN n)} {φ' : Proposition (LIinfN n)} (h : Sim (XinfAt t) φ') :
    φ' = XinfAt t := by
  obtain ⟨w, rfl, hw⟩ := h
  rcases hw with hw | ⟨hr, -⟩
  · rw [← hw]; rfl
  · exact absurd trivial hr

theorem nX_sim {t : SyntacticTerm (LIinfN n)} {φ' : Proposition (LIinfN n)}
    (h : Sim (∼(XinfAt t)) φ') : φ' = ∼(XinfAt t) := by
  obtain ⟨w, rfl, hw⟩ := h
  rcases hw with hw | ⟨hr, -⟩
  · rw [← hw]; rfl
  · exact absurd trivial hr

/-- The statement of term replacement for a derivation of `Δ`. -/
def ReplClaim (A : Fin n → Semisentence (LXIn n) 1) (ρ : ThetaWNoteD)
    (H : Set ThetaWNoteD → Set ThetaWNoteD) (α : ThetaWNoteD) (Δ : Sequent (LIinfN n)) : Prop :=
  ThetaWNoteD.IsOperator H → ∀ Γ' : Sequent (LIinfN n), (∀ φ ∈ Δ, ∃ φ' ∈ Γ', Sim φ φ') →
    paramsVal Γ' ⊆ H ∅ → IDnDerivable A ρ H α Γ'

theorem cover_cons {Δ Γ' : Sequent (LIinfN n)} {φ φ' : Proposition (LIinfN n)} (h : Sim φ φ')
    (hΔ : ∀ ψ ∈ Δ, ∃ ψ' ∈ Γ', Sim ψ ψ') : ∀ ψ ∈ φ :: Δ, ∃ ψ' ∈ φ' :: Γ', Sim ψ ψ' := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact ⟨φ', List.mem_cons_self, h⟩
  · obtain ⟨ψ', h1, h2⟩ := hΔ ψ hψ
    exact ⟨ψ', List.mem_cons_of_mem _ h1, h2⟩

theorem params_cons_sub {H : Set ThetaWNoteD → Set ThetaWNoteD} {Γ' : Sequent (LIinfN n)}
    {φ φ' : Proposition (LIinfN n)} (h : Sim φ φ') (hφ : Stage.val '' params φ ⊆ H ∅)
    (hΓ : paramsVal Γ' ⊆ H ∅) : paramsVal (φ' :: Γ') ⊆ H ∅ := by
  rw [paramsVal_cons, h.params_eq]
  exact Set.union_subset hφ hΓ

theorem replace_aux (hA : ∀ k, XFreeL (A k)) {H : Set ThetaWNoteD → Set ThetaWNoteD}
    {α : ThetaWNoteD} {Δ : Sequent (LIinfN n)} (d : IDnDerivable A ρ H α Δ) : ReplClaim A ρ H α Δ := by
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
    exact .all f hα hP hχ hf fun p =>
      ih0 p hH _ (cover_cons (s'.subst_numI p) hΔ)
        (params_cons_sub (s'.subst_numI p) (d0 p).params_head_subset hP)
  | exs p hα _ hm hn h0 d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hs⟩ := hΔ _ hm
    obtain ⟨ψ', rfl, s'⟩ := hs
    exact .exs p hα hP hχ hn h0
      (ih0 hH _ (cover_cons (s'.subst_numI p) hΔ)
        (params_cons_sub (s'.subst_numI p) d0.params_head_subset hP))
  | stage g hα _ hm hga hgα hgH h0 d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hs⟩ := hΔ _ hm
    obtain ⟨t', rfl, ht⟩ := stage_sim hs
    have s' := sim_unfold (hA _) g ht
    exact .stage g hα hP hχ hga hgα hgH h0
      (ih0 hH _ (cover_cons s' hΔ) (params_cons_sub s' d0.params_head_subset hP))
  | @nstage H' α' Δ' k a t f hα _ hm hf d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hs⟩ := hΔ _ hm
    obtain ⟨t', rfl, ht⟩ := nstage_sim hs
    refine .nstage f hα hP hχ hf fun g hg => ?_
    have s' := (sim_unfold (hA k) g ht).neg
    have hsub : H' ∅ ⊆ ThetaWNoteD.adjoin H' {g.1} ∅ := hH.mono (Set.empty_subset _)
    exact ih0 g hg (hH.adjoin {g.1}) _ (cover_cons s' hΔ)
      (params_cons_sub s' (d0 g hg).params_head_subset (hP.trans hsub))
  | @fix H' α' Δ' k t α₀' hα _ hm hΩ h0 d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hs⟩ := hΔ _ hm
    obtain ⟨t', rfl, ht⟩ := stage_sim hs
    have s' := sim_unfold (hA k) (StageAt.top k.val) ht
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
theorem IDnDerivable.replace (hA : ∀ k, XFreeL (A k)) {H : Set ThetaWNoteD → Set ThetaWNoteD}
    (hH : ThetaWNoteD.IsOperator H) {α : ThetaWNoteD} {Γ Γ' : Sequent (LIinfN n)}
    (d : IDnDerivable A ρ H α Γ) (hΓ : ∀ φ ∈ Γ, ∃ φ' ∈ Γ', Sim φ φ')
    (hP : paramsVal Γ' ⊆ H ∅) : IDnDerivable A ρ H α Γ' :=
  replace_aux hA d hH Γ' hΓ hP

/-- Term replacement in the head formula. -/
theorem IDnDerivable.replace_head (hA : ∀ k, XFreeL (A k)) {H : Set ThetaWNoteD → Set ThetaWNoteD}
    (hH : ThetaWNoteD.IsOperator H) {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    {φ φ' : Proposition (LIinfN n)} (d : IDnDerivable A ρ H α (φ :: Γ)) (h : Sim φ φ') :
    IDnDerivable A ρ H α (φ' :: Γ) := by
  refine d.replace hA hH (cover_cons h fun ψ hψ => ⟨ψ, hψ, Sim.refl ψ⟩) ?_
  have hP := d.params_subset
  rw [paramsVal_cons] at hP ⊢
  rw [h.params_eq]
  exact hP

end Replace

end IDn

end OrdinalAnalysis
