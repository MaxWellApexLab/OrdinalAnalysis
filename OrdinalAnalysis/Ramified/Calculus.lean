/-
  The infinitary ramified calculus `RA_∞`, design D2.

  This is `Omega/Calculus.lean` with two changes and two new rules.

  * **Cut ranks are ordinal notations**, as in `ACAOmega/Calculus.lean`: a cut on
    `φ` is allowed at rank `ρ` when `rank φ < ρ`.  Heights stay a generic
    `[OrdinalNotation O]`.  The rank lives in `Gamma0Note` because a level-`ν`
    set atom costs up to `blkTop ν`, `ω·ν` at a finite `ν` (`Ramified/Rank.lean`).

  * **The instantiation must not raise the rank** (`InstantiationR.rank_nf`,
    and numerals that are ground terms denoting their own index).
    `Instantiation` only promises `complexity_nf`, which is the right law when
    cuts are ranked by complexity; here the cut rule reads `rank`, and the
    quantifier and (Pr) cases of the reduction lemma produce cut formulas that
    are instances, so their rank has to be at most the rank of the body
    (`InstantiationR.rank_inst_le`).  The rank of a (Pr) atom reads the stage of
    the code its set argument denotes, so the numerals must denote.

  * **The two predicator rules.**  From `Γ, A_a(n̄)` conclude `Γ, n̄ ∈̇_ν ā`, and
    dually from `Γ, ∼A_a(n̄)` conclude `Γ, n̄ ∉̇_ν ā`, where `ν = lvl a` and
    `A_a = body a` is the body of the code `a`.  Nothing else is new: a level-`ν`
    set quantifier is a number quantifier over codes, so the ω-rule and `exs`
    already handle it.

  Two design decisions recorded here because the prototype had to make them.

  **Identity is atomic**, as in `Omega/Calculus.lean`, not general as in
  `ACAOmega/Calculus.lean`.  `ACAOmega` needs general identity because its
  (∀₂)/(∃₂) reduction substitutes a *formula* for an eigenvariable, and that
  substitution must preserve heights exactly — with atomic identity the leaf
  `[t ∈ X, t ∉ X]` at height `0` becomes `[ψ(t), ∼ψ(t)]`, derivable only at
  height `2·complexity ψ`, which `redOrd β γ` has no room for.  D2 has no
  formula-for-variable substitution anywhere: the only substitution is of a
  *term* into the body of a code, and `rank_subst₁_le` says that does not raise
  the rank.  So the reason for general identity is gone, and atomic identity is kept
  — which in turn keeps `Omega/Reduction.lean`'s identity case verbatim.

  **The instantiation supplies the (Pr) subject.**  The premise is
  `I.inst (body a) n`, not `(body a)/[t]` for a free-floating term `t`.  The
  reason is the one `Omega/Calculus.lean` gives for the ω-rule: closed terms have
  to be identified with their values, or an embedding that evaluates has nothing
  to feed the rule.  It also makes the (Pr) premise a *function of the
  conclusion*, which is what the reduction lemma's principal case needs.

  One side condition on the atomic axioms, recorded as `MemFree`: **no axiom
  is the conclusion of a predicator rule**.  `Literals` only asks that axioms be
  literals and be consistent, and a set atom *is* a literal — so without
  `MemFree` an axiom could be `n̄ ∉̇_ν ā` with `a` a `Good` code of level `ν`,
  and a (Pr)/axiom cut would have no principal reduction.  Negated set atoms at
  names that denote no `Good` code of their level are allowed: they are what
  makes such a name denote the empty set.  This is the analogue of
  `StandardLX.lean`'s `trueArithLits_xfree`, which excludes `X`-literals from
  the axioms for the same kind of reason.
-/
import OrdinalAnalysis.Ramified.Rank

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Derivation

/-! ### The instantiation -/

/-- An `Instantiation` of `LRA` that also preserves the rank.

`Instantiation.complexity_nf` is the law a complexity-ranked calculus consumes;
`rank_nf` is its analogue for an ordinal-ranked one.  The numerals are ground
and denote their index: the rank of a (Pr) atom reads the stage of the code its
set argument denotes. -/
structure InstantiationR extends Instantiation LRA where
  /-- The normaliser preserves the rank. -/
  rank_nf : ∀ φ : Proposition LRA, rank (nf φ) = rank φ
  /-- The numerals are ground terms. -/
  num_ground : ∀ n : ℕ, GroundR (num n)
  /-- The numeral of `n` denotes `n`. -/
  num_val : ∀ n : ℕ, evTermR (num n) = n
  /-- Distinct numbers get distinct numerals.

  Not needed by the *principal* (Pr)/(Pr) case, but needed by the dispatcher
  that reaches it: two (Pr) inferences whose conclusions are the same atom must
  be shown to be inferences on the same code and the same subject, and the atom
  only records the two numerals.  `num_injective` discharges it for the standard
  numeral family. -/
  num_inj : Function.Injective num

namespace InstantiationR

variable (I : InstantiationR)

/-- The `n`-th instance of a body. -/
def inst (φ : Semiproposition LRA 1) (n : ℕ) : Proposition LRA :=
  I.toInstantiation.inst φ n

@[simp] theorem inst_neg (φ : Semiproposition LRA 1) (n : ℕ) :
    I.inst (∼φ) n = ∼I.inst φ n := I.toInstantiation.inst_neg φ n

/-- **The rank of an instance is at most the rank of the body.**  The law the
(Pr) and quantifier cases of the reduction lemma consume. -/
theorem rank_inst_le (φ : Semiproposition LRA 1) (n : ℕ) :
    rank (I.inst φ n) ≤ rank φ := by
  simp only [inst, Instantiation.inst, I.rank_nf]
  exact rank_subst₁_le φ _

/-- Plain substitution, with no normalisation. -/
def raw (numf : ℕ → SyntacticTerm LRA) (hnum : Function.Injective numf)
    (hg : ∀ n, GroundR (numf n)) (hv : ∀ n, evTermR (numf n) = n) : InstantiationR where
  toInstantiation := Instantiation.raw numf
  rank_nf := fun _ => rfl
  num_inj := hnum
  num_ground := hg
  num_val := hv

@[simp] theorem raw_num (numf : ℕ → SyntacticTerm LRA) (hnum : Function.Injective numf)
    (hg : ∀ n, GroundR (numf n)) (hv : ∀ n, evTermR (numf n) = n) :
    (raw numf hnum hg hv).num = numf := rfl

@[simp] theorem raw_inst (numf : ℕ → SyntacticTerm LRA) (hnum : Function.Injective numf)
    (hg : ∀ n, GroundR (numf n)) (hv : ∀ n, evTermR (numf n) = n)
    (φ : Semiproposition LRA 1) (n : ℕ) :
    (raw numf hnum hg hv).inst φ n = φ/[numf n] := by
  simp [inst, Instantiation.inst, raw, Instantiation.raw]

/-- **The standard instantiation**: Foundation's numerals, no normalisation.
Exists, so nothing above is vacuous. -/
def std : InstantiationR := raw num num_injective groundR_num evTermR_num

end InstantiationR

/-! ### The side condition on the atomic axioms

A set atom is a literal, so `Literals` alone does not stop one from being an
axiom — and then a (Pr) inference and an axiom could cut against each other with
no principal reduction available.  `MemFree` excludes exactly that: no positive
set atom is an axiom, and a negated set atom `t ∉̇_ν s` is an axiom only when `s`
is ground and does not denote a `Good` code of level `ν`.  Such an atom is never
the conclusion of a (Pr⁻) inference, so it meets a (Pr) atom only through a cut on
a literal, which is the existing literal case of the reduction lemma.  The
negated *junk* atoms are the axioms that make a non-`Good` name denote the empty
set (`Ramified/Literals.lean`'s `junkLitsR`); the true closed arithmetic
literals satisfy the condition on the nose. -/

/-- **No axiom is a (Pr) or (Pr⁻) conclusion**: no positive set atom is an axiom,
and a negated set atom is one only at a ground name that denotes no `Good` code
of its level. -/
def MemFree (A : Literals LRA) : Prop :=
  ∀ φ : Proposition LRA, A.T φ → ∀ (ν : Lv) (t s : SyntacticTerm LRA),
    φ ≠ memAt ν t s ∧
      (φ = nmemAt ν t s → GroundR s ∧ ¬(Good (evTermR s) ∧ lvl (evTermR s) = ν))

namespace MemFree

variable {A : Literals LRA} (h : MemFree A)
include h

theorem ne_memAt {φ : Proposition LRA} (hφ : A.T φ) (ν : Lv) (t s : SyntacticTerm LRA) :
    φ ≠ memAt ν t s := (h φ hφ ν t s).1

/-- **No axiom is a (Pr⁻) conclusion.** -/
theorem ne_nmemAt {φ : Proposition LRA} (hφ : A.T φ) (I : InstantiationR) {a : ℕ}
    (ha : Good a) (n : ℕ) : φ ≠ nmemAt (lvl a) (I.num n) (I.num a) := by
  intro he
  have hbad := ((h φ hφ _ _ _).2 he).2
  rw [I.num_val] at hbad
  exact hbad ⟨ha, rfl⟩

end MemFree

/-! ### The calculus -/

/-- **Derivability in `RA_∞`**, at cut rank `ρ`, of height below `α`, with
quantifier instances supplied by `I` and atomic axioms by `A`. -/
inductive OmegaDerivableR {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
    (A : Literals LRA) (I : InstantiationR) (ρ : Gamma0Note) : O → Sequent LRA → Prop
  | atom {α : O} {φ : Proposition LRA} :
      A.T φ → OmegaDerivableR A I ρ α [φ]
  | identity {α : O} {k : ℕ} (rl : LRA.Rel k) (v) :
      OmegaDerivableR A I ρ α [.rel rl v, .nrel rl v]
  | verum {α : O} :
      OmegaDerivableR A I ρ α [⊤]
  | or {α β : O} {φ ψ : Proposition LRA} {Γ : Sequent LRA} :
      β < α → OmegaDerivableR A I ρ β (φ :: ψ :: Γ) →
      OmegaDerivableR A I ρ α (φ ⋎ ψ :: Γ)
  | and {α β γ : O} {φ ψ : Proposition LRA} {Γ : Sequent LRA} :
      β < α → γ < α →
      OmegaDerivableR A I ρ β (φ :: Γ) → OmegaDerivableR A I ρ γ (ψ :: Γ) →
      OmegaDerivableR A I ρ α (φ ⋏ ψ :: Γ)
  | omegaRule {α : O} {φ : Semiproposition LRA 1} {Γ : Sequent LRA} (β : ℕ → O) :
      (∀ n, β n < α) →
      (∀ n : ℕ, OmegaDerivableR A I ρ (β n) (I.inst φ n :: Γ)) →
      OmegaDerivableR A I ρ α ((∀¹ φ) :: Γ)
  | exs {α β : O} {φ : Semiproposition LRA 1} {Γ : Sequent LRA} (n : ℕ) :
      β < α → OmegaDerivableR A I ρ β (I.inst φ n :: Γ) →
      OmegaDerivableR A I ρ α ((∃¹ φ) :: Γ)
  | contraction {α : O} {Δ Γ : Sequent LRA} :
      Δ ⊆ Γ → OmegaDerivableR A I ρ α Δ →
      OmegaDerivableR A I ρ α Γ
  | cut {α β γ : O} {φ : Proposition LRA} {Γ Δ : Sequent LRA} :
      rank φ < ρ → β < α → γ < α →
      OmegaDerivableR A I ρ β (φ :: Γ) → OmegaDerivableR A I ρ γ (∼φ :: Δ) →
      OmegaDerivableR A I ρ α (Γ ++ Δ)
  /-- **(Pr).**  From `Γ, A_a(n̄)` conclude `Γ, n̄ ∈̇_{lvl a} ā`. -/
  | pr {α β : O} {a n : ℕ} {Γ : Sequent LRA} :
      Good a → β < α →
      OmegaDerivableR A I ρ β (I.inst (body a) n :: Γ) →
      OmegaDerivableR A I ρ α (memAt (lvl a) (I.num n) (I.num a) :: Γ)
  /-- **(Pr⁻).**  The negative twin: from `Γ, ∼A_a(n̄)` conclude
  `Γ, n̄ ∉̇_{lvl a} ā`. -/
  | npr {α β : O} {a n : ℕ} {Γ : Sequent LRA} :
      Good a → β < α →
      OmegaDerivableR A I ρ β (∼(I.inst (body a) n) :: Γ) →
      OmegaDerivableR A I ρ α (nmemAt (lvl a) (I.num n) (I.num a) :: Γ)

namespace OmegaDerivableR

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals LRA} {I : InstantiationR}

/-- Weakening in the ordinal index. -/
theorem mono_ord {ρ : Gamma0Note} {α β : O} {Γ : Sequent LRA}
    (h : OmegaDerivableR A I ρ α Γ) (hab : α ≤ β) : OmegaDerivableR A I ρ β Γ := by
  induction h generalizing β with
  | atom h => exact .atom h
  | identity rl v => exact .identity rl v
  | verum => exact .verum
  | or hlt _ ih => exact .or (lt_of_lt_of_le hlt hab) (ih le_rfl)
  | and h₁ h₂ _ _ ih₁ ih₂ =>
      exact .and (lt_of_lt_of_le h₁ hab) (lt_of_lt_of_le h₂ hab) (ih₁ le_rfl) (ih₂ le_rfl)
  | omegaRule f hf _ ih =>
      exact .omegaRule f (fun n => lt_of_lt_of_le (hf n) hab) (fun n => ih n le_rfl)
  | exs n hlt _ ih => exact .exs n (lt_of_lt_of_le hlt hab) (ih le_rfl)
  | contraction ss _ ih => exact .contraction ss (ih hab)
  | cut hc h₁ h₂ _ _ ih₁ ih₂ =>
      exact .cut hc (lt_of_lt_of_le h₁ hab) (lt_of_lt_of_le h₂ hab) (ih₁ le_rfl) (ih₂ le_rfl)
  | pr ha hlt _ ih => exact .pr ha (lt_of_lt_of_le hlt hab) (ih le_rfl)
  | npr ha hlt _ ih => exact .npr ha (lt_of_lt_of_le hlt hab) (ih le_rfl)

/-- Weakening in the cut rank. -/
theorem mono_rank {ρ σ : Gamma0Note} {α : O} {Γ : Sequent LRA}
    (h : OmegaDerivableR A I ρ α Γ) (hρσ : ρ ≤ σ) : OmegaDerivableR A I σ α Γ := by
  induction h with
  | atom h => exact .atom h
  | identity rl v => exact .identity rl v
  | verum => exact .verum
  | or hlt _ ih => exact .or hlt ih
  | and h₁ h₂ _ _ ih₁ ih₂ => exact .and h₁ h₂ ih₁ ih₂
  | omegaRule f hf _ ih => exact .omegaRule f hf ih
  | exs n hlt _ ih => exact .exs n hlt ih
  | contraction ss _ ih => exact .contraction ss ih
  | cut hc h₁ h₂ _ _ ih₁ ih₂ => exact .cut (lt_of_lt_of_le hc hρσ) h₁ h₂ ih₁ ih₂
  | pr ha hlt _ ih => exact .pr ha hlt ih
  | npr ha hlt _ ih => exact .npr ha hlt ih

/-- **Weakening in the atomic axioms.**  More axioms, the same derivations. -/
theorem mono_lits {B : Literals LRA} (hAB : ∀ φ, A.T φ → B.T φ) {ρ : Gamma0Note} {α : O}
    {Γ : Sequent LRA} (h : OmegaDerivableR A I ρ α Γ) : OmegaDerivableR B I ρ α Γ := by
  induction h with
  | atom h => exact .atom (hAB _ h)
  | identity rl v => exact .identity rl v
  | verum => exact .verum
  | or hlt _ ih => exact .or hlt ih
  | and h₁ h₂ _ _ ih₁ ih₂ => exact .and h₁ h₂ ih₁ ih₂
  | omegaRule f hf _ ih => exact .omegaRule f hf ih
  | exs n hlt _ ih => exact .exs n hlt ih
  | contraction ss _ ih => exact .contraction ss ih
  | cut hc h₁ h₂ _ _ ih₁ ih₂ => exact .cut hc h₁ h₂ ih₁ ih₂
  | pr ha hlt _ ih => exact .pr ha hlt ih
  | npr ha hlt _ ih => exact .npr ha hlt ih

/-- A sequent carrying an atom together with its negation is derivable outright. -/
theorem of_mem_identity {ρ : Gamma0Note} {α : O} {Θ : Sequent LRA} {k : ℕ}
    (rl : LRA.Rel k) (v) (hp : Semiformula.rel rl v ∈ Θ)
    (hn : Semiformula.nrel rl v ∈ Θ) : OmegaDerivableR A I ρ α Θ := by
  refine .contraction ?_ (.identity rl v)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hp
  · exact hn

/-- `⊤` in a sequent makes it derivable outright. -/
theorem of_mem_verum {ρ : Gamma0Note} {α : O} {Θ : Sequent LRA}
    (h : (⊤ : Proposition LRA) ∈ Θ) : OmegaDerivableR A I ρ α Θ := by
  refine .contraction ?_ .verum
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl
  exact h

/-- If the head of a derivable sequent already occurs in its tail, drop it. -/
theorem drop_head {ρ : Gamma0Note} {α : O} {ψ : Proposition LRA} {Θ : Sequent LRA}
    (h : OmegaDerivableR A I ρ α (ψ :: Θ)) (hmem : ψ ∈ Θ) : OmegaDerivableR A I ρ α Θ := by
  refine .contraction ?_ h
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hmem
  · exact hx

/-- Contract a doubled sequent.  The shape every principal case of the reduction
lemma ends in: a cut delivers `Θ ++ Θ`. -/
theorem of_append_self {ρ : Gamma0Note} {α : O} {Θ : Sequent LRA}
    (h : OmegaDerivableR A I ρ α (Θ ++ Θ)) : OmegaDerivableR A I ρ α Θ := by
  refine .contraction ?_ h
  intro x hx
  simp only [List.mem_append] at hx
  tauto

/-! ### The (Pr) rules, in the form the reduction lemma uses -/

/-- The atom a (Pr) inference concludes. -/
abbrev prAtom (I : InstantiationR) (a n : ℕ) : Proposition LRA :=
  memAt (lvl a) (I.num n) (I.num a)

@[simp] theorem neg_prAtom (I : InstantiationR) (a n : ℕ) :
    ∼(prAtom I a n) = nmemAt (lvl a) (I.num n) (I.num a) := rfl

/-- **A (Pr) atom's unfolding has rank below the atom's.**  The atom costs
`blk (lvl a) ⊕ stage a`, the unfolding at most `blk (lvl a)` plus the
complexity and the parameter's stage (`rank_body_lt_memRank`).  The inequality
the (Pr)/(Pr) cut turns on. -/
theorem rank_inst_body_lt_rank_prAtom {a : ℕ} (ha : Good a) (n : ℕ) :
    rank (I.inst (body a) n) < rank (prAtom I a n) := by
  rw [prAtom, rank_memAt]
  exact lt_of_le_of_lt (I.rank_inst_le (body a) n)
    (rank_body_lt_memRank ha (I.num_ground a) (I.num_val a))

/-- **A (Pr) atom determines the code and the subject.**

This is what lets the reduction lemma's dispatcher conclude that two (Pr)
inferences with the same conclusion have the *same* premise — which is what the
principal case assumes.  It needs nothing but `num_inj`; the level is carried by
the relation symbol and so is read off directly. -/
theorem prAtom_inj {a n a' n' : ℕ} (h : prAtom I a n = prAtom I a' n') :
    a = a' ∧ n = n' := by
  obtain ⟨_, ht, hs⟩ := memAt_inj h
  exact ⟨I.num_inj hs, I.num_inj ht⟩

/-- The negated form, which is the shape the right-hand derivation presents. -/
theorem nprAtom_inj {a n a' n' : ℕ}
    (h : nmemAt (lvl a) (I.num n) (I.num a) = nmemAt (lvl a') (I.num n') (I.num a')) :
    a = a' ∧ n = n' := by
  obtain ⟨_, ht, hs⟩ := nmemAt_inj h
  exact ⟨I.num_inj hs, I.num_inj ht⟩

end OmegaDerivableR

end Ramified

end OrdinalAnalysis
