/- Source: OrdinalAnalysis\IDn\Evaluate.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.Calculus
import OrdinalAnalysis.Ordinal.ThetaV.WellFoundedV
/-
  Closed terms and their values in the infinitary calculus of `ID_ω`: one binary inductively
  defined predicate `J`, stage predicates `I_k^{≺α}` and `Jlev ℓ`, levels `k : ℕ`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §6: the remark in the proof of Proposition 6.4
  ("we can replace any occurrence of `t` by the numeral with the same value, since the
  notion of false literal in Definition 5.1 is unaffected"), used again for the
  existential quantifier in the proof of Theorem 6.5; after Exercise 3.5 of the first
  lecture. Port of `IDn/Evaluate.lean`.

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
  are `X`-free automatically in `IDw` (the operator form `A : FormJ` lives in `LForm`, which
  has only `P`, `Q`; `xFreeI_unfold_body`), since the stage rules move the term into
  `A_k(t, I_k^{≺γ})`.  The two rules `jlev`/`njlev` inspect their first argument only through
  its value `termVal s`, and are handled by `jlev_sim`/`njlev_sim`.

  **The relation.**  `TEq s t`: `s = t`, or both are free of free variables and have the
  same value under every assignment.  `Sim φ ψ`: `ψ` is `φ` with some arguments of
  arithmetic and stage literals replaced by `TEq`-related terms.  Then

      H ⊢^α_ρ Γ,  every formula of Γ is Sim-related to a formula of Γ'
        ⇒  H ⊢^α_ρ Γ'                                       (`IDwDerivable.replace`),

  which also contains weakening in the sequent.

  **`IsXRelN`/`XFreeI`/`XFreeL`/`xFreeI_rew` are also used by `IDw/NumSubst.lean`**, which
  imports this file.  The numeral lemmas (`val_numI`, `numI_freeVariables`, `termVal_numI`)
  live in `IDw/CalculusAux.lean`.

  Contents.

    (numerals denote their values: `val_numI` etc., in `IDw/CalculusAux.lean`)
    `closedVal`, `val_closed`                the value of a closed term
    `ThetaVNoteD.le_omegaMul`                `α ⪯ ω · α` (by well-foundedness)
    `IsXRelN`, `XFreeI`, `XFreeL`            formulas without the free predicate `X`
    `TEq`, `RelOK`, `Sim`                    the replacement relation
    `Sim.refl`, `Sim.neg`, `Sim.params_eq`, `Sim.rew`, `Sim.trueLit`
    `Sim.of_rew_pair`                        two closed instances of the same formula
    `sim_subst_closed`, `sim_subst_numI`     `ψ(s) ~ ψ(t)` for closed `s`, `t` of equal value
    `IDwDerivable.replace`, `replace_head`   **term replacement**
-/

set_option autoImplicit false

namespace OrdinalAnalysis


/-! ### Numerals denote their values: `val_numI`, `termVal_numI`, `numI_freeVariables` live in
`IDw/CalculusAux.lean` (imported through `IDw.Calculus`). -/

namespace IDw

open LO LO.FirstOrder

/-! ### Formulas without `X`

`XFreeL` is over `LXJ` (the theory's language, with `X` and `J`), for `IDw/NumSubst.lean`; the
operator forms live in `LForm` and are `X`-free by construction (`xFreeI_lMap_formHomAt`). -/

section XFree

variable {ξ : Type*}

/-- `r` is the free predicate `X`. -/
def IsXRelN : {k : ℕ} → (LIinfW).Rel k → Prop
  | _, Sum.inl _ => False
  | _, Sum.inr IInfRelW.X => True
  | _, Sum.inr (IInfRelW.stage _) => False
  | _, Sum.inr (IInfRelW.jlev _) => False

/-- A formula of `LIinfW` without the free predicate `X`. -/
def XFreeI : {m : ℕ} → Semiformula (LIinfW) ξ m → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel r _ => ¬IsXRelN r
  | _, .nrel r _ => ¬IsXRelN r
  | _, .and φ ψ => XFreeI φ ∧ XFreeI ψ
  | _, .or φ ψ => XFreeI φ ∧ XFreeI ψ
  | _, .all φ => XFreeI φ
  | _, .exs φ => XFreeI φ

/-- A formula of `LXJ` without the free predicate `X`. -/
def XFreeL : {m : ℕ} → Semiformula (LXJ) ξ m → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel (Sum.inl _) _ => True
  | _, .rel (Sum.inr XJRel.X) _ => False
  | _, .rel (Sum.inr XJRel.J) _ => True
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr XJRel.X) _ => False
  | _, .nrel (Sum.inr XJRel.J) _ => True
  | _, .and φ ψ => XFreeL φ ∧ XFreeL ψ
  | _, .or φ ψ => XFreeL φ ∧ XFreeL ψ
  | _, .all φ => XFreeL φ
  | _, .exs φ => XFreeL φ

@[simp] theorem xFreeI_neg {m : ℕ} (φ : Semiformula (LIinfW) ξ m) : XFreeI (∼φ) ↔ XFreeI φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v => exact Iff.rfl
  | hnrel r v => exact Iff.rfl
  | hand φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | hor φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | hall φ ih => exact ih
  | hexs φ ih => exact ih

@[simp] theorem xFreeI_rew {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfW) ξ₁ m₁ ξ₂ m₂)
    (φ : Semiformula (LIinfW) ξ₁ m₁) : XFreeI (ω ▹ φ) ↔ XFreeI φ := by
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

/-- The operator forms of `IDw` (`FormJ = Semisentence LForm 2`) mention no free predicate `X`
(the language `LForm` has only `P`, `Q`), so every unfolding `formAtW A k a` is `X`-free. -/
theorem xFreeI_lMap_formHomAt (k : ℕ) (a : StageAt k) {m : ℕ} :
    ∀ (φ : Semiformula LForm ξ m), XFreeI (Semiformula.lMap (formHomAt k a) φ)
  | .verum => trivial
  | .falsum => trivial
  | .rel (Sum.inl _) _ => fun h => h
  | .rel (Sum.inr PQRel.P) _ => fun h => h
  | .rel (Sum.inr PQRel.Q) _ => fun h => h
  | .nrel (Sum.inl _) _ => fun h => h
  | .nrel (Sum.inr PQRel.P) _ => fun h => h
  | .nrel (Sum.inr PQRel.Q) _ => fun h => h
  | .and φ ψ => ⟨xFreeI_lMap_formHomAt k a φ, xFreeI_lMap_formHomAt k a ψ⟩
  | .or φ ψ => ⟨xFreeI_lMap_formHomAt k a φ, xFreeI_lMap_formHomAt k a ψ⟩
  | .all φ => xFreeI_lMap_formHomAt k a φ
  | .exs φ => xFreeI_lMap_formHomAt k a φ

/-- For every operator form, every unfolding is `X`-free. -/
theorem xFreeI_unfold_body (A : FormJ) (k : ℕ) (a : StageAt k) :
    XFreeI (Rewriting.emb (formAtW A k a) : Semiformula (LIinfW) ℕ 2) :=
  (xFreeI_rew _ _).mpr (xFreeI_lMap_formHomAt k a A)

end XFree



/-- Every rewriting fixes a numeral. -/
@[simp] theorem rew_numeral {ξ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfW) ξ m₁ ξ m₂) (p : ℕ) :
    ω ((p : ℕ) : Semiterm (LIinfW) ξ m₁) = ((p : ℕ) : Semiterm (LIinfW) ξ m₂) := by
  simp

/-! ### The value of a closed term -/

/-- The value of a closed term in the standard structure. -/
def closedVal (t : SyntacticTerm (LIinfW)) : ℕ :=
  Semiterm.val (s := stdW) ![] (fun _ => 0) t

/-- The value of a term without free variables does not depend on the assignment. -/
theorem val_closed {t : SyntacticTerm (LIinfW)} (ht : t.freeVariables = ∅) (e : Fin 0 → ℕ)
    (ε : ℕ → ℕ) : Semiterm.val (s := stdW) e ε t = closedVal t := by
  unfold closedVal
  have he : e = ![] := funext fun i => i.elim0
  subst he
  refine Semiterm.val_eq_of_funEqOn t ?_
  intro x hx
  have hx' : x ∈ t.freeVariables := hx
  rw [ht] at hx'
  exact absurd hx' (Finset.notMem_empty x)

@[simp] theorem closedVal_numI (p : ℕ) : closedVal (numI p) = p := val_numI p ![] _

end IDw

/-! ### `α ⪯ ω · α` -/

namespace ThetaVNoteD

/-- **`α ⪯ ω · α`**: a strictly increasing map of a well-order is inflationary. -/
theorem le_omegaMul (a : ThetaVNoteD) : a ≤ ThetaVNoteD.omegaMul a := by
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    by_contra h
    have hlt : ThetaVNoteD.omegaMul a < a := lt_of_not_ge h
    have h1 := ih _ hlt
    exact absurd (ThetaVNoteD.omegaMul_lt_omegaMul hlt) (not_lt_of_ge h1)

end ThetaVNoteD

namespace IDw

open LO LO.FirstOrder

/-! ### The replacement relation -/

section Sim

variable {ξ : Type*} {m : ℕ}

/-- `s` and `t` are equal, or both are free of free variables and have the same value under
every assignment. -/
def TEq {m : ℕ} (s t : Semiterm (LIinfW) ℕ m) : Prop :=
  s = t ∨ (s.freeVariables = ∅ ∧ t.freeVariables = ∅ ∧
    ∀ (e : Fin m → ℕ) (ε : ℕ → ℕ),
      Semiterm.val (s := stdW) e ε s = Semiterm.val (s := stdW) e ε t)

/-- The arguments of a literal may be replaced, unless the literal is an `X`-literal. -/
def RelOK {m k : ℕ} (r : (LIinfW).Rel k) (v w : Fin k → Semiterm (LIinfW) ℕ m) : Prop :=
  v = w ∨ (¬IsXRelN r ∧ ∀ i, TEq (v i) (w i))

/-- **`Sim φ ψ`**: `ψ` is `φ` with some arguments of arithmetic and stage literals replaced by
`TEq`-related terms. -/
def Sim : {m : ℕ} → Semiformula (LIinfW) ℕ m → Semiformula (LIinfW) ℕ m → Prop
  | _, .verum, ψ => ψ = ⊤
  | _, .falsum, ψ => ψ = ⊥
  | _, .rel r v, ψ => ∃ w, ψ = .rel r w ∧ RelOK r v w
  | _, .nrel r v, ψ => ∃ w, ψ = .nrel r w ∧ RelOK r v w
  | _, .and φ₁ φ₂, ψ => ∃ ψ₁ ψ₂, ψ = ψ₁ ⋏ ψ₂ ∧ Sim φ₁ ψ₁ ∧ Sim φ₂ ψ₂
  | _, .or φ₁ φ₂, ψ => ∃ ψ₁ ψ₂, ψ = ψ₁ ⋎ ψ₂ ∧ Sim φ₁ ψ₁ ∧ Sim φ₂ ψ₂
  | _, .all φ, ψ => ∃ ψ', ψ = ∀¹ ψ' ∧ Sim φ ψ'
  | _, .exs φ, ψ => ∃ ψ', ψ = ∃¹ ψ' ∧ Sim φ ψ'

theorem TEq.refl {m : ℕ} (t : Semiterm (LIinfW) ℕ m) : TEq t t := Or.inl rfl

theorem RelOK.refl {m k : ℕ} (r : (LIinfW).Rel k) (v : Fin k → Semiterm (LIinfW) ℕ m) :
    RelOK r v v := Or.inl rfl

theorem Sim.refl {m : ℕ} (φ : Semiformula (LIinfW) ℕ m) : Sim φ φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact rfl
  | hfalsum => exact rfl
  | hrel r v => exact ⟨v, rfl, RelOK.refl r v⟩
  | hnrel r v => exact ⟨v, rfl, RelOK.refl r v⟩
  | hand φ ψ ihφ ihψ => exact ⟨φ, ψ, rfl, ihφ, ihψ⟩
  | hor φ ψ ihφ ihψ => exact ⟨φ, ψ, rfl, ihφ, ihψ⟩
  | hall φ ih => exact ⟨φ, rfl, ih⟩
  | hexs φ ih => exact ⟨φ, rfl, ih⟩

theorem Sim.neg {m : ℕ} {φ ψ : Semiformula (LIinfW) ℕ m} (h : Sim φ ψ) : Sim (∼φ) (∼ψ) := by
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
theorem Sim.params_eq {m : ℕ} {φ ψ : Semiformula (LIinfW) ℕ m} (h : Sim φ ψ) :
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
theorem freeVariables_rew_term {m₁ m₂ : ℕ} (ω : Rew (LIinfW) ℕ m₁ ℕ m₂)
    (hb : ∀ x, (ω #x).freeVariables = ∅) :
    ∀ {t : Semiterm (LIinfW) ℕ m₁}, t.freeVariables = ∅ → (ω t).freeVariables = ∅ := by
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

theorem freeVariables_bShift {m : ℕ} (t : Semiterm (LIinfW) ℕ m) :
    (Rew.bShift t).freeVariables = t.freeVariables := by
  ext x
  exact Semiterm.fvar?_bShift

/-- The rewritings that keep `Sim`: the bound variables go to terms without free
variables. -/
def BClosed {m₁ m₂ : ℕ} (ω : Rew (LIinfW) ℕ m₁ ℕ m₂) : Prop :=
  ∀ x, (ω #x).freeVariables = ∅

theorem BClosed.q {m₁ m₂ : ℕ} {ω : Rew (LIinfW) ℕ m₁ ℕ m₂} (h : BClosed ω) : BClosed ω.q := by
  intro x
  cases x using Fin.cases with
  | zero => rw [Rew.q_bvar_zero]; rfl
  | succ x => rw [Rew.q_bvar_succ, freeVariables_bShift]; exact h x

theorem TEq.rew {m₁ m₂ : ℕ} {ω : Rew (LIinfW) ℕ m₁ ℕ m₂} (hω : BClosed ω)
    {s t : Semiterm (LIinfW) ℕ m₁} (h : TEq s t) : TEq (ω s) (ω t) := by
  rcases h with rfl | ⟨hs, ht, hv⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨freeVariables_rew_term ω hω hs, freeVariables_rew_term ω hω ht, ?_⟩
    intro e ε
    rw [Semiterm.val_rew, Semiterm.val_rew]
    exact hv _ _

theorem RelOK.rew {m₁ m₂ k : ℕ} {ω : Rew (LIinfW) ℕ m₁ ℕ m₂} (hω : BClosed ω)
    {r : (LIinfW).Rel k} {v w : Fin k → Semiterm (LIinfW) ℕ m₁} (h : RelOK r v w) :
    RelOK r (ω ∘ v) (ω ∘ w) := by
  rcases h with rfl | ⟨hr, h⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hr, fun i => (h i).rew hω⟩

/-- **`Sim` is stable under rewritings whose bound-variable images have no free variables**,
in particular under the instantiation of a quantifier at a numeral. -/
theorem Sim.rew {m₁ : ℕ} {φ ψ : Semiformula (LIinfW) ℕ m₁} (h : Sim φ ψ) :
    ∀ {m₂ : ℕ} {ω : Rew (LIinfW) ℕ m₁ ℕ m₂}, BClosed ω → Sim (ω ▹ φ) (ω ▹ ψ) := by
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
    BClosed (Rew.subst ![numI p] : Rew (LIinfW) ℕ 1 ℕ 0) := by
  intro x
  cases x using Fin.cases with
  | zero => simpa using numI_freeVariables p
  | succ x => exact x.elim0

theorem Sim.subst_numI {φ ψ : Semiformula (LIinfW) ℕ 1} (h : Sim φ ψ) (p : ℕ) :
    Sim (φ/[numI p]) (ψ/[numI p]) :=
  h.rew (bClosed_subst_numI p)

/-- **The truth of an arithmetic literal sees only the values of its arguments.** -/
theorem Sim.trueLit {φ ψ : Proposition (LIinfW)} (h : Sim φ ψ) (hφ : TrueLit φ) : TrueLit ψ := by
  obtain ⟨⟨j, r, v, hform, hv⟩, htrue⟩ := hφ
  have key : ∀ w : Fin j → SyntacticTerm (LIinfW), RelOK (Sum.inl r : (LIinfW).Rel j) v w →
      (∀ i, (w i).freeVariables = ∅) ∧
        (fun i => Semiterm.val (s := stdW) ![] (fun _ => 0) (v i)) =
          (fun i => Semiterm.val (s := stdW) ![] (fun _ => 0) (w i)) := by
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
    have ht : Semiformula.Eval (s := stdW) ![] (fun _ => 0)
        (Semiformula.rel (Sum.inl r : (LIinfW).Rel j) v) := htrue
    have hval' : (Semiterm.val (s := stdW) ![] (fun _ => 0) ∘ v) =
        (Semiterm.val (s := stdW) ![] (fun _ => 0) ∘ w) := hval
    exact (Semiformula.eval_rel (s := stdW) (r := (Sum.inl r : (LIinfW).Rel j))).mpr
      (hval' ▸ (Semiformula.eval_rel (s := stdW) (r := (Sum.inl r : (LIinfW).Rel j))).mp ht)
  · obtain ⟨w, rfl, hw⟩ := h
    obtain ⟨hw', hval⟩ := key w hw
    refine ⟨⟨j, r, w, Or.inr rfl, hw'⟩, ?_⟩
    have ht : Semiformula.Eval (s := stdW) ![] (fun _ => 0)
        (Semiformula.nrel (Sum.inl r : (LIinfW).Rel j) v) := htrue
    have hval' : (Semiterm.val (s := stdW) ![] (fun _ => 0) ∘ v) =
        (Semiterm.val (s := stdW) ![] (fun _ => 0) ∘ w) := hval
    exact (Semiformula.eval_nrel (s := stdW) (r := (Sum.inl r : (LIinfW).Rel j))).mpr
      (hval' ▸ (Semiformula.eval_nrel (s := stdW) (r := (Sum.inl r : (LIinfW).Rel j))).mp ht)

/-- Two rewritings that send the bound variables to terms without free variables of equal
values, and agree on the free variables. -/
def PairOK {m₁ m₂ : ℕ} (ω ω' : Rew (LIinfW) ℕ m₁ ℕ m₂) : Prop :=
  (∀ x, (ω #x).freeVariables = ∅ ∧ (ω' #x).freeVariables = ∅ ∧
    ∀ (e : Fin m₂ → ℕ) (ε : ℕ → ℕ),
      Semiterm.val (s := stdW) e ε (ω #x) = Semiterm.val (s := stdW) e ε (ω' #x)) ∧
  ∀ x, ω &x = ω' &x

theorem PairOK.q {m₁ m₂ : ℕ} {ω ω' : Rew (LIinfW) ℕ m₁ ℕ m₂} (h : PairOK ω ω') :
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

theorem PairOK.teq {m₁ m₂ : ℕ} {ω ω' : Rew (LIinfW) ℕ m₁ ℕ m₂} (h : PairOK ω ω')
    {t : Semiterm (LIinfW) ℕ m₁} (ht : t.freeVariables = ∅) : TEq (ω t) (ω' t) := by
  refine Or.inr ⟨freeVariables_rew_term ω (fun x => (h.1 x).1) ht,
    freeVariables_rew_term ω' (fun x => (h.1 x).2.1) ht, fun e ε => ?_⟩
  rw [Semiterm.val_rew, Semiterm.val_rew]
  congr 1
  · funext x; exact (h.1 x).2.2 e ε
  · funext x; simp only [Function.comp_apply, h.2 x]

theorem freeVariables_rel_arg {m k : ℕ} {r : (LIinfW).Rel k}
    {v : Fin k → Semiterm (LIinfW) ℕ m} (h : (Semiformula.rel r v).freeVariables = ∅)
    (i : Fin k) : (v i).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have : x ∈ (Semiformula.rel r v).freeVariables := by
    rw [Semiformula.freeVariables_rel]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  rw [h] at this
  exact Finset.notMem_empty x this

theorem freeVariables_nrel_arg {m k : ℕ} {r : (LIinfW).Rel k}
    {v : Fin k → Semiterm (LIinfW) ℕ m} (h : (Semiformula.nrel r v).freeVariables = ∅)
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
theorem Sim.of_rew_pair {m₁ : ℕ} {φ : Semiformula (LIinfW) ℕ m₁} (hφ : φ.freeVariables = ∅)
    (hX : XFreeI φ) :
    ∀ {m₂ : ℕ} {ω ω' : Rew (LIinfW) ℕ m₁ ℕ m₂}, PairOK ω ω' → Sim (ω ▹ φ) (ω' ▹ φ) := by
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
theorem sim_subst_closed {m : ℕ} {φ : Semiformula (LIinfW) ℕ 1} (hφ : φ.freeVariables = ∅)
    (hX : XFreeI φ) {s t : Semiterm (LIinfW) ℕ m} (hs : s.freeVariables = ∅)
    (ht : t.freeVariables = ∅)
    (hv : ∀ (e : Fin m → ℕ) (ε : ℕ → ℕ),
      Semiterm.val (s := stdW) e ε s = Semiterm.val (s := stdW) e ε t) :
    Sim (Rew.subst ![s] ▹ φ) (Rew.subst ![t] ▹ φ) := by
  refine Sim.of_rew_pair hφ hX ⟨fun x => ?_, fun x => ?_⟩
  · cases x using Fin.cases with
    | zero => simpa using ⟨hs, ht, hv⟩
    | succ x => exact x.elim0
  · simp

/-- **Freund's remark**: a closed term may be replaced by the numeral of its value. -/
theorem sim_subst_numI {φ : Semiformula (LIinfW) ℕ 1} (hφ : φ.freeVariables = ∅) (hX : XFreeI φ)
    {t : SyntacticTerm (LIinfW)} (ht : t.freeVariables = ∅) :
    Sim (φ/[t]) (φ/[numI (closedVal t)]) :=
  sim_subst_closed hφ hX ht (numI_freeVariables _) (fun e ε => by
    rw [val_closed ht, val_numI])

theorem TEq.sim_subst {φ : Semiformula (LIinfW) ℕ 1} (hφ : φ.freeVariables = ∅) (hX : XFreeI φ)
    {t t' : SyntacticTerm (LIinfW)} (h : TEq t t') : Sim (φ/[t]) (φ/[t']) := by
  rcases h with rfl | ⟨hs, ht, hv⟩
  · exact Sim.refl _
  · exact sim_subst_closed hφ hX hs ht hv

end Sim

/-! ### Term replacement -/

section Replace

variable {A : Semisentence LForm 2} {ρ : ThetaVNoteD}

/-- The unfolding at two `TEq`-related terms (the second bound variable is the numeral `k̄`, the
same on both sides). -/
theorem sim_unfold {k : ℕ} (g : StageAt k)
    {t t' : SyntacticTerm (LIinfW)} (h : TEq t t') :
    Sim (unfoldW A k g t) (unfoldW A k g t') := by
  rcases h with rfl | ⟨hs, ht, hv⟩
  · exact Sim.refl _
  · refine Sim.of_rew_pair (Semiformula.freeVariables_emb _) (xFreeI_unfold_body A k g)
      ⟨fun x => ?_, fun x => ?_⟩
    · cases x using Fin.cases with
      | zero =>
        have e0 : (Rew.subst ![t, Semiterm.numeral k] : Rew (LIinfW) ℕ 2 ℕ 0) #0 = t := by simp
        have e0' : (Rew.subst ![t', Semiterm.numeral k] : Rew (LIinfW) ℕ 2 ℕ 0) #0 = t' := by simp
        rw [e0, e0']
        exact ⟨hs, ht, hv⟩
      | succ x =>
        cases x using Fin.cases with
        | zero => exact ⟨numeral_freeVariables k, numeral_freeVariables k, fun _ _ => rfl⟩
        | succ x => exact x.elim0
    · simp

/-- A binary negated atom is `nrel r ![v 0, v 1]`. -/
theorem nrel_eq_vec2 {ξ : Type*} {k : ℕ} (r : (LIinfW).Rel 2) (v : Fin 2 → Semiterm (LIinfW) ξ k) :
    Semiformula.nrel r v = Semiformula.nrel r ![v 0, v 1] := by
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

/-- A unary negated atom is `nrel r ![v 0]`. -/
theorem nrel_eq_vec {ξ : Type*} {k : ℕ} (r : (LIinfW).Rel 1) (v : Fin 1 → Semiterm (LIinfW) ξ k) :
    Semiformula.nrel r v = Semiformula.nrel r ![v 0] := by
  congr 1; funext i; obtain rfl := Subsingleton.elim i 0; rfl

theorem stage_sim {s : Stage} {t : SyntacticTerm (LIinfW)} {φ' : Proposition (LIinfW)}
    (h : Sim (stageAt s t) φ') : ∃ t', φ' = stageAt s t' ∧ TEq t t' := by
  obtain ⟨w, rfl, hw⟩ := h
  refine ⟨w 0, rel_eq_vec _ w, ?_⟩
  rcases hw with hw | ⟨-, hw⟩
  · rw [← hw]; exact TEq.refl _
  · exact hw 0

theorem nstage_sim {s : Stage} {t : SyntacticTerm (LIinfW)} {φ' : Proposition (LIinfW)}
    (h : Sim (nstageAt s t) φ') : ∃ t', φ' = nstageAt s t' ∧ TEq t t' := by
  obtain ⟨w, rfl, hw⟩ := h
  refine ⟨w 0, nrel_eq_vec _ w, ?_⟩
  rcases hw with hw | ⟨-, hw⟩
  · rw [← hw]; exact TEq.refl _
  · exact hw 0

/-- A `Jlev` atom (binary): its two arguments are replaced by `TEq`-related terms. -/
theorem jlev_sim {ℓ : WithTop ℕ} {s t : SyntacticTerm (LIinfW)} {φ' : Proposition (LIinfW)}
    (h : Sim (jlevAt ℓ s t) φ') : ∃ s' t', φ' = jlevAt ℓ s' t' ∧ TEq s s' ∧ TEq t t' := by
  obtain ⟨w, rfl, hw⟩ := h
  refine ⟨w 0, w 1, rel_eq_vec2 _ w, ?_⟩
  rcases hw with hw | ⟨-, hw⟩
  · subst hw; exact ⟨TEq.refl _, TEq.refl _⟩
  · exact ⟨hw 0, hw 1⟩

/-- A negated `Jlev` atom (binary). -/
theorem njlev_sim {ℓ : WithTop ℕ} {s t : SyntacticTerm (LIinfW)} {φ' : Proposition (LIinfW)}
    (h : Sim (njlevAt ℓ s t) φ') : ∃ s' t', φ' = njlevAt ℓ s' t' ∧ TEq s s' ∧ TEq t t' := by
  obtain ⟨w, rfl, hw⟩ := h
  refine ⟨w 0, w 1, nrel_eq_vec2 _ w, ?_⟩
  rcases hw with hw | ⟨-, hw⟩
  · subst hw; exact ⟨TEq.refl _, TEq.refl _⟩
  · exact ⟨hw 0, hw 1⟩

/-- A closed term `TEq`-related to another has the same value, and the other is closed. -/
theorem TEq.closed_val {s s' : SyntacticTerm (LIinfW)} (hs : s.freeVariables = ∅)
    (h : TEq s s') : s'.freeVariables = ∅ ∧ termVal s' = termVal s := by
  rcases h with rfl | ⟨-, hs', hv⟩
  · exact ⟨hs, rfl⟩
  · exact ⟨hs', (hv ![] (fun _ => 0)).symm⟩

/-- `I_{k}^{≺a} t ~ I_{k}^{≺a} t'` for `TEq`-related `t`, `t'`. -/
theorem sim_stageAt {a : Stage} {t t' : SyntacticTerm (LIinfW)} (h : TEq t t') :
    Sim (stageAt a t) (stageAt a t') :=
  ⟨![t'], rfl, Or.inr ⟨fun h => h, fun i => by obtain rfl := Subsingleton.elim i 0; exact h⟩⟩

theorem X_sim {t : SyntacticTerm (LIinfW)} {φ' : Proposition (LIinfW)} (h : Sim (XinfAt t) φ') :
    φ' = XinfAt t := by
  obtain ⟨w, rfl, hw⟩ := h
  rcases hw with hw | ⟨hr, -⟩
  · rw [← hw]; rfl
  · exact absurd trivial hr

theorem nX_sim {t : SyntacticTerm (LIinfW)} {φ' : Proposition (LIinfW)}
    (h : Sim (∼(XinfAt t)) φ') : φ' = ∼(XinfAt t) := by
  obtain ⟨w, rfl, hw⟩ := h
  rcases hw with hw | ⟨hr, -⟩
  · rw [← hw]; rfl
  · exact absurd trivial hr

/-- The statement of term replacement for a derivation of `Δ`. -/
def ReplClaim (A : Semisentence LForm 2) (ρ : ThetaVNoteD)
    (H : Set ThetaVNoteD → Set ThetaVNoteD) (α : ThetaVNoteD) (Δ : Sequent (LIinfW)) : Prop :=
  ThetaVNoteD.IsOperator H → ∀ Γ' : Sequent (LIinfW), (∀ φ ∈ Δ, ∃ φ' ∈ Γ', Sim φ φ') →
    paramsVal Γ' ⊆ H ∅ → IDwDerivable A ρ H α Γ'

theorem cover_cons {Δ Γ' : Sequent (LIinfW)} {φ φ' : Proposition (LIinfW)} (h : Sim φ φ')
    (hΔ : ∀ ψ ∈ Δ, ∃ ψ' ∈ Γ', Sim ψ ψ') : ∀ ψ ∈ φ :: Δ, ∃ ψ' ∈ φ' :: Γ', Sim ψ ψ' := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact ⟨φ', List.mem_cons_self, h⟩
  · obtain ⟨ψ', h1, h2⟩ := hΔ ψ hψ
    exact ⟨ψ', List.mem_cons_of_mem _ h1, h2⟩

theorem params_cons_sub {H : Set ThetaVNoteD → Set ThetaVNoteD} {Γ' : Sequent (LIinfW)}
    {φ φ' : Proposition (LIinfW)} (h : Sim φ φ') (hφ : Stage.val '' params φ ⊆ H ∅)
    (hΓ : paramsVal Γ' ⊆ H ∅) : paramsVal (φ' :: Γ') ⊆ H ∅ := by
  rw [paramsVal_cons, h.params_eq]
  exact Set.union_subset hφ hΓ

theorem replace_aux {H : Set ThetaVNoteD → Set ThetaVNoteD}
    {α : ThetaVNoteD} {Δ : Sequent (LIinfW)} (d : IDwDerivable A ρ H α Δ) : ReplClaim A ρ H α Δ := by
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
    have s' := sim_unfold (A := A) g ht
    exact .stage g hα hP hχ hga hgα hgH h0
      (ih0 hH _ (cover_cons s' hΔ) (params_cons_sub s' d0.params_head_subset hP))
  | @nstage H' α' Δ' k a t f hα _ hm hf d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hs⟩ := hΔ _ hm
    obtain ⟨t', rfl, ht⟩ := nstage_sim hs
    refine .nstage f hα hP hχ hf fun g hg => ?_
    have s' := (sim_unfold (A := A) g ht).neg
    have hsub : H' ∅ ⊆ ThetaVNoteD.adjoin H' {g.1} ∅ := hH.mono (Set.empty_subset _)
    exact ih0 g hg (hH.adjoin {g.1}) _ (cover_cons s' hΔ)
      (params_cons_sub s' (d0 g hg).params_head_subset (hP.trans hsub))
  | @fix H' α' Δ' k t α₀' hα _ hm hΩ h0 d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hs⟩ := hΔ _ hm
    obtain ⟨t', rfl, ht⟩ := stage_sim hs
    have s' := sim_unfold (A := A) (StageAt.top k) ht
    exact .fix hα hP hχ hΩ h0
      (ih0 hH _ (cover_cons s' hΔ) (params_cons_sub s' d0.params_head_subset hP))
  | @jlev _ _ _ _ s t _ hα _ hm hs ht hl h0 d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hsim⟩ := hΔ _ hm
    obtain ⟨s', t', rfl, hss, htt⟩ := jlev_sim hsim
    obtain ⟨hs', vs⟩ := hss.closed_val hs
    obtain ⟨ht', -⟩ := htt.closed_val ht
    have s₁ : Sim (IOmegaAt (termVal s) t) (IOmegaAt (termVal s') t') := by
      rw [vs]; exact sim_stageAt htt
    exact .jlev hα hP hχ hs' ht' (by rw [vs]; exact hl) h0
      (ih0 hH _ (cover_cons s₁ hΔ) (params_cons_sub s₁ d0.params_head_subset hP))
  | @njlev _ _ _ _ s t _ hα _ hm hs ht h0 d0 ih0 =>
    intro hH Γ' hΔ hP
    obtain ⟨χ, hχ, hsim⟩ := hΔ _ hm
    obtain ⟨s', t', rfl, hss, htt⟩ := njlev_sim hsim
    obtain ⟨hs', vs⟩ := hss.closed_val hs
    obtain ⟨ht', -⟩ := htt.closed_val ht
    have s₁ : Sim (∼(IOmegaAt (termVal s) t)) (∼(IOmegaAt (termVal s') t')) := by
      rw [vs]; exact (sim_stageAt htt).neg
    exact .njlev hα hP hχ hs' ht' (fun h => h0 (by rw [vs] at h; exact h))
      (fun h => by
        rw [vs] at h
        exact ih0 h hH _ (cover_cons s₁ hΔ) (params_cons_sub s₁ (d0 h).params_head_subset hP))
  | cut hα _ hr h0 d0 d1 ih0 ih1 =>
    intro hH Γ' hΔ hP
    exact .cut hα hP hr h0
      (ih0 hH _ (cover_cons (Sim.refl _) hΔ)
        (params_cons_sub (Sim.refl _) d0.params_head_subset hP))
      (ih1 hH _ (cover_cons (Sim.refl _) hΔ)
        (params_cons_sub (Sim.refl _) d1.params_head_subset hP))

/-- **Term replacement** (Freund, proof of Proposition 6.4): if every formula of `Γ` is
`Sim`-related to a formula of `Γ'`, then `H ⊢^α_ρ Γ` gives `H ⊢^α_ρ Γ'`. -/
theorem IDwDerivable.replace {H : Set ThetaVNoteD → Set ThetaVNoteD}
    (hH : ThetaVNoteD.IsOperator H) {α : ThetaVNoteD} {Γ Γ' : Sequent (LIinfW)}
    (d : IDwDerivable A ρ H α Γ) (hΓ : ∀ φ ∈ Γ, ∃ φ' ∈ Γ', Sim φ φ')
    (hP : paramsVal Γ' ⊆ H ∅) : IDwDerivable A ρ H α Γ' :=
  replace_aux d hH Γ' hΓ hP

/-- Term replacement in the head formula. -/
theorem IDwDerivable.replace_head {H : Set ThetaVNoteD → Set ThetaVNoteD}
    (hH : ThetaVNoteD.IsOperator H) {α : ThetaVNoteD} {Γ : Sequent (LIinfW)}
    {φ φ' : Proposition (LIinfW)} (d : IDwDerivable A ρ H α (φ :: Γ)) (h : Sim φ φ') :
    IDwDerivable A ρ H α (φ' :: Γ) := by
  refine d.replace hH (cover_cons h fun ψ hψ => ⟨ψ, hψ, Sim.refl ψ⟩) ?_
  have hP := d.params_subset
  rw [paramsVal_cons] at hP ⊢
  rw [h.params_eq]
  exact hP

end Replace

end IDw

end OrdinalAnalysis
