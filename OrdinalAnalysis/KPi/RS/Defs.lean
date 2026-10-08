import Mathlib.Data.Fin.VecNotation
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular

/-!
# The RS calculus of Buchholz 1992 (B92), part 1: terms, sentences, rank, junctor

B92 = W. Buchholz, "A simplified version of local predicativity" (1992), Section 1.

* `D0 n`   : the RS-formulas, i.e. the relativised `Delta_0`-formulas of `L_Ad` (atoms `in`, `not in`,
             `Ad`, `not Ad`; `and`, `or`; bounded quantifiers), in de Bruijn form.  The bound of a
             quantifier is a variable (holding an RS-term) or a level constant `L_alpha`.
* `PT`, `T`: RS-terms (B92 Def 1.1): `L_alpha` and `[x in L_alpha : phi(x, a_1, .., a_n)]`; `T` is the
             type of the well-formed ones.
* `RSS`    : RS-sentences: a `D0`-formula with an environment of RS-terms, closed under `and`/`or`.
* `RSS.rk`, `RSS.k` : rank (B92 Def 1.8) and level set `k` (Def 1.2), computed from summaries of the
             environment (the rank of `A(c)` depends only on the rank of `c`).
* `expand` : the junctor `A ~ \/ (A_i)` or `/\ (A_i)` of B92 Def 1.6, parametric in the class `R`.

All ordinals are `Ordinal.{1}`, so the syntactic types live in `Type 2`.  The language `L_Ad` itself
(Foundation formulas) is `OrdinalAnalysis.KPi.LAd`; the RS calculus works with its own `D0`.
-/

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

/-! ### environments -/

/-- extend an environment by one (innermost) entry, at index `Fin.last`. -/
abbrev ext {X : Sort*} {n : ℕ} (e : Fin n → X) (x : X) : Fin (n + 1) → X :=
  Fin.snoc (α := fun _ => X) e x

@[simp] theorem ext_last {X : Sort*} {n : ℕ} (e : Fin n → X) (x : X) : ext e x (Fin.last n) = x := by
  simp [ext]

@[simp] theorem ext_castSucc {X : Sort*} {n : ℕ} (e : Fin n → X) (x : X) (i : Fin n) :
    ext e x i.castSucc = e i := by
  simp [ext]

/-! ### RS-formulas -/

/-- the bound of a quantifier: a variable, or the level constant `L_α`. -/
inductive Bd (n : ℕ) : Type 2
  | var (i : Fin n)
  | lev (α : Ordinal.{1})

/-- RS-formulas: `Δ₀`-formulas of `L_Ad` (atoms `∈, ∉, Ad, ¬Ad`; `∧ ∨`; bounded `∃ ∀`), de Bruijn.
`bex b A` is `∃x∈b A` with `x` the new variable `Fin.last n`. -/
inductive D0 : ℕ → Type 2
  | mem  {n : ℕ} (i j : Fin n) : D0 n
  | nmem {n : ℕ} (i j : Fin n) : D0 n
  | ad   {n : ℕ} (i : Fin n) : D0 n
  | nad  {n : ℕ} (i : Fin n) : D0 n
  | and  {n : ℕ} (A B : D0 n) : D0 n
  | or   {n : ℕ} (A B : D0 n) : D0 n
  | bex  {n : ℕ} (b : Bd n) (A : D0 (n + 1)) : D0 n
  | ball {n : ℕ} (b : Bd n) (A : D0 (n + 1)) : D0 n

namespace D0

/-- negation, defined by De Morgan (B92 Def 1.6, item 5, and p.3). -/
def neg : {n : ℕ} → D0 n → D0 n
  | _, mem i j => nmem i j
  | _, nmem i j => mem i j
  | _, ad i => nad i
  | _, nad i => ad i
  | _, and A B => or (neg A) (neg B)
  | _, or A B => and (neg A) (neg B)
  | _, bex b A => ball b (neg A)
  | _, ball b A => bex b (neg A)

@[simp] theorem neg_neg : ∀ {n : ℕ} (A : D0 n), A.neg.neg = A
  | _, mem _ _ => rfl
  | _, nmem _ _ => rfl
  | _, ad _ => rfl
  | _, nad _ => rfl
  | _, and A B => by simp [neg, neg_neg A, neg_neg B]
  | _, or A B => by simp [neg, neg_neg A, neg_neg B]
  | _, bex b A => by simp [neg, neg_neg A]
  | _, ball b A => by simp [neg, neg_neg A]

/-- `u ⊆ v := ∀x∈u (x ∈ v)`. -/
def subset {n : ℕ} (i j : Fin n) : D0 n :=
  ball (Bd.var i) (mem (Fin.last n) j.castSucc)

/-- `u = v := u ⊆ v ∧ v ⊆ u` (B92 abbreviation; `=` is not primitive in `L_Ad`). -/
def eqf {n : ℕ} (i j : Fin n) : D0 n := and (subset i j) (subset j i)

/-- all level constants occurring as bounds are `≤ α`. -/
def LevLE : {n : ℕ} → Ordinal.{1} → D0 n → Prop
  | _, _, mem _ _ => True
  | _, _, nmem _ _ => True
  | _, _, ad _ => True
  | _, _, nad _ => True
  | _, α, and A B => LevLE α A ∧ LevLE α B
  | _, α, or A B => LevLE α A ∧ LevLE α B
  | _, α, bex (Bd.var _) A => LevLE α A
  | _, α, bex (Bd.lev γ) A => γ ≤ α ∧ LevLE α A
  | _, α, ball (Bd.var _) A => LevLE α A
  | _, α, ball (Bd.lev γ) A => γ ≤ α ∧ LevLE α A

/-- the variable `i` occurs (free) in `φ` (B92 Def 1.1 asks that `x` occurs in the body of a term;
this gives `k(ι) ⊆ k(A_ι)`, Lemma 1.9 (c)). -/
def Occ : {n : ℕ} → Fin n → D0 n → Prop
  | _, i, mem a b => i = a ∨ i = b
  | _, i, nmem a b => i = a ∨ i = b
  | _, i, ad a => i = a
  | _, i, nad a => i = a
  | _, i, and A B => Occ i A ∨ Occ i B
  | _, i, or A B => Occ i A ∨ Occ i B
  | _, i, bex (Bd.var j) A => i = j ∨ Occ i.castSucc A
  | _, i, bex (Bd.lev _) A => Occ i.castSucc A
  | _, i, ball (Bd.var j) A => i = j ∨ Occ i.castSucc A
  | _, i, ball (Bd.lev _) A => Occ i.castSucc A

end D0

/-! ### RS-terms -/

/-- pre-terms: `L_α` and `[x ∈ L_α : φ(x, a₁,…,aₙ)]` (the body `φ` already relativised to `L_α`:
its bounds are variables or level constants; the variable `Fin.last n` is `x`). -/
inductive PT : Type 2
  | L (α : Ordinal.{1}) : PT
  | sep (α : Ordinal.{1}) {n : ℕ} (φ : D0 (n + 1)) (a : Fin n → PT) : PT

/-- the level `|t|` of a term. -/
def PT.level : PT → Ordinal.{1}
  | .L α => α
  | .sep α _ _ => α

/-- well-formedness (B92 Def 1.1): `α > 0`; parameters are well-formed of level `< α`;
level constants in the body are `≤ α`; `x` occurs in the body. -/
def PT.Wf : PT → Prop
  | .L _ => True
  | .sep α φ a => 0 < α ∧ D0.LevLE α φ ∧ (∀ i, PT.Wf (a i) ∧ PT.level (a i) < α) ∧
      D0.Occ (Fin.last _) φ

/-- the class `𝒯` of RS-terms. -/
abbrev T : Type 2 := {t : PT // t.Wf}

def T.L (α : Ordinal.{1}) : T := ⟨.L α, trivial⟩

/-- the level `|t|`. -/
def T.level (t : T) : Ordinal.{1} := t.1.level

/-- `𝒯_α = {t | |t| < α}`. -/
abbrev Tlt (α : Ordinal.{1}) : Type 2 := {t : T // t.level < α}

/-! ### rank and level sets, by summaries of the environment -/

open Ordinal

noncomputable section

def rkBd {n : ℕ} : Bd n → (Fin n → Ordinal.{1}) → Ordinal.{1}
  | .var i, e => e i
  | .lev α, _ => ω * α

/-- B92 Def 1.8, on formulas whose free variables carry ranks `e`. -/
def rkD : {n : ℕ} → D0 n → (Fin n → Ordinal.{1}) → Ordinal.{1}
  | _, .mem i j, e => max (e i + 6) (e j + 1)
  | _, .nmem i j, e => max (e i + 6) (e j + 1)
  | _, .ad i, e => e i + 5
  | _, .nad i, e => e i + 5
  | _, .and A B, e => max (rkD A e) (rkD B e) + 1
  | _, .or A B, e => max (rkD A e) (rkD B e) + 1
  | _, .bex b A, e => max (rkBd b e) (rkD A (ext e 0) + 2)
  | _, .ball b A, e => max (rkBd b e) (rkD A (ext e 0) + 2)

def PT.rk : PT → Ordinal.{1}
  | .L α => ω * α
  | .sep α φ a => max (ω * α + 1) (rkD φ (ext (fun i => (a i).rk) 0) + 2)

def T.rk (t : T) : Ordinal.{1} := t.1.rk

def kBd {n : ℕ} : Bd n → (Fin n → Set Ordinal.{1}) → Set Ordinal.{1}
  | .var i, e => e i
  | .lev α, _ => {α}

/-- B92 Def 1.2: the set of `α` such that `L_α` occurs. -/
def kD : {n : ℕ} → D0 n → (Fin n → Set Ordinal.{1}) → Set Ordinal.{1}
  | _, .mem i j, e => e i ∪ e j
  | _, .nmem i j, e => e i ∪ e j
  | _, .ad i, e => e i
  | _, .nad i, e => e i
  | _, .and A B, e => kD A e ∪ kD B e
  | _, .or A B, e => kD A e ∪ kD B e
  | _, .bex b A, e => kBd b e ∪ kD A (ext e ∅)
  | _, .ball b A, e => kBd b e ∪ kD A (ext e ∅)

def PT.k : PT → Set Ordinal.{1}
  | .L α => {α}
  | .sep α φ a => {α} ∪ kD φ (ext (fun i => (a i).k) ∅)

def T.k (t : T) : Set Ordinal.{1} := t.1.k

end

/-! ### RS-sentences -/

/-- RS-sentences: a formula with an environment of terms, and `and`/`or` of sentences. -/
inductive RSS : Type 2
  | base {n : ℕ} (φ : D0 n) (ρ : Fin n → T) : RSS
  | and (A B : RSS) : RSS
  | or (A B : RSS) : RSS

namespace RSS

def neg : RSS → RSS
  | base φ ρ => base φ.neg ρ
  | and A B => or (neg A) (neg B)
  | or A B => and (neg A) (neg B)

@[simp] theorem neg_neg : ∀ A : RSS, A.neg.neg = A
  | base φ ρ => by simp [neg]
  | and A B => by simp [neg, neg_neg A, neg_neg B]
  | or A B => by simp [neg, neg_neg A, neg_neg B]

noncomputable def rk : RSS → Ordinal.{1}
  | base φ ρ => rkD φ (fun i => (ρ i).rk)
  | and A B => max A.rk B.rk + 1
  | or A B => max A.rk B.rk + 1

def k : RSS → Set Ordinal.{1}
  | base φ ρ => kD φ (fun i => (ρ i).k)
  | and A B => A.k ∪ B.k
  | or A B => A.k ∪ B.k

end RSS

/-- `a =ᵣ b` as a sentence: `a ⊆ b ∧ b ⊆ a` (B92 abbreviation). -/
def eqS (a b : T) : RSS := .base (D0.eqf 0 1) ![a, b]

/-- `t ∈° b` (B92 Def 1.3): `B(t)` if `b ≡ [x∈L_β : B(x)]`, and `t ∉ L_0` if `b ≡ L_β`. -/
def memInst (t b : T) : RSS :=
  match b with
  | ⟨.L _, _⟩ => .base (D0.nmem 0 1) ![t, T.L 0]
  | ⟨.sep _ φ a, hb⟩ => .base φ (ext (fun i => (⟨a i, (hb.2.2.1 i).1⟩ : T)) t)

/-- the junctor `A ≃ ⋁(A_ι)_{ι∈J}` or `⋀(A_ι)_{ι∈J}` of B92 Def 1.6. -/
structure Junct : Type 3 where
  isOr : Bool
  J : Type 2
  lvl : J → Ordinal.{1}
  ks : J → Set Ordinal.{1}
  child : J → RSS

/-- the two-element index set `{0,1}` (in `Type 2`). -/
abbrev Two : Type 2 := ULift.{2} Bool

section Expand

variable (R : Set Ordinal.{1})

/-- the index set `{κ ∈ R : κ ≤ |a|}` of `Ad(a)` (`R` consists of `ε`-numbers, so `0 < κ` is automatic in B92;
we build it into the index set so that no hypothesis on `R` is needed for the rank lemma). -/
abbrev AdIdx (a : T) : Type 2 := {κ : Ordinal.{1} // κ ∈ R ∧ 0 < κ ∧ κ ≤ a.level}

def resBd {n : ℕ} : Bd n → (Fin n → T) → T
  | .var i, ρ => ρ i
  | .lev α, _ => T.L α

/-- one-step unfolding of an RS-sentence (B92 Def 1.6). -/
def expandD : {n : ℕ} → D0 n → (Fin n → T) → Junct
  | _, .mem i j, ρ =>
      ⟨true, Tlt (ρ j).level, fun t => t.1.level, fun t => t.1.k,
        fun t => .and (memInst t.1 (ρ j)) (eqS t.1 (ρ i))⟩
  | _, .nmem i j, ρ =>
      ⟨false, Tlt (ρ j).level, fun t => t.1.level, fun t => t.1.k,
        fun t => .or (memInst t.1 (ρ j)).neg (eqS t.1 (ρ i)).neg⟩
  | _, .ad i, ρ =>
      ⟨true, AdIdx R (ρ i), fun κ => κ.1, fun κ => {κ.1}, fun κ => eqS (T.L κ.1) (ρ i)⟩
  | _, .nad i, ρ =>
      ⟨false, AdIdx R (ρ i), fun κ => κ.1, fun κ => {κ.1}, fun κ => (eqS (T.L κ.1) (ρ i)).neg⟩
  | _, .and A B, ρ =>
      ⟨false, Two, fun _ => 0, fun _ => ∅, fun b => cond b.down (.base A ρ) (.base B ρ)⟩
  | _, .or A B, ρ =>
      ⟨true, Two, fun _ => 0, fun _ => ∅, fun b => cond b.down (.base A ρ) (.base B ρ)⟩
  | _, .bex b A, ρ =>
      ⟨true, Tlt (resBd b ρ).level, fun t => t.1.level, fun t => t.1.k,
        fun t => .and (memInst t.1 (resBd b ρ)) (.base A (ext ρ t.1))⟩
  | _, .ball b A, ρ =>
      ⟨false, Tlt (resBd b ρ).level, fun t => t.1.level, fun t => t.1.k,
        fun t => .or (memInst t.1 (resBd b ρ)).neg (.base A (ext ρ t.1))⟩

def expand : RSS → Junct
  | .base φ ρ => expandD R φ ρ
  | .and A B => ⟨false, Two, fun _ => 0, fun _ => ∅, fun b => cond b.down A B⟩
  | .or A B => ⟨true, Two, fun _ => 0, fun _ => ∅, fun b => cond b.down A B⟩

end Expand

end OrdinalAnalysis.KPi.RS
