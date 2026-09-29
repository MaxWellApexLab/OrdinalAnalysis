/-
  The language `ℒ_Ad` of the KPi station (Buchholz 1992, "Notation systems for infinitary
  derivations / Simplified local predicativity", section 1, p.3): the language of set theory
  whose ONLY non-logical symbol is the binary predicate `∈`, plus the unary predicate `Ad`
  ("admissible").

  **Design decisions (recorded in the design notes).**

    * We do NOT reuse Foundation's `ℒₛₑₜ`.  `ℒₛₑₜ` carries a PRIMITIVE equality symbol; B92 has
      none (`u = v` is the DEFINED formula `u ⊆ v ∧ v ⊆ u`, and its axiom (Ext) is exactly the
      substitutivity statement that makes the defined equality a congruence for `∈` and `Ad`).
      An idle primitive `eq` would have to be interpreted in the RS term model of K1-R and would
      invite formulas B92 does not have.  So `LAd` has exactly the two relation symbols `∈`, `Ad`,
      no function symbols, and we hook it into Foundation through `Language.Mem` (which makes
      Foundation's `Operator.Mem`, `Semiformula.ballMem`, and the quote notation `“x ∈ y”`
      available).
    * Foundation's `Semiformula` is in negation normal form (`nrel`, `∼` is de Morgan
      dualisation, `φ 🡒 ψ := ∼φ ⋎ ψ`), which is literally B92's convention: atoms are `u ∈ v`,
      `¬(u ∈ v)`, `Ad(u)`, `¬Ad(u)`; `¬A` is defined by de Morgan's laws.
    * Bound variables are de Bruijn indices; `#0` is the innermost binder.  The bounding term
      of a restricted quantifier is `Rew.bShift t`, which can never be `#0`, so B92's side
      condition `x ≢ v` holds by construction.

  Contents.

    `AdRel`, `LAd`, `Language.Mem LAd`            the language
    `memAt`, `nmemAt`, `adAt`, `nadAt`             the four atoms
    `ballAt`, `bexAt`                              restricted quantifiers `∀x∈t φ`, `∃x∈t φ`
    `subsetAt`, `eqAt`, `tranAt`, `infiniteAt`     B92's abbreviations `u ⊆ v`, `u = v`,
                                                   `tran(u)`, `infinite(u)` (p.3)
-/
import Foundation.FirstOrder.Basic

set_option autoImplicit false

namespace OrdinalAnalysis

namespace KPi

open LO LO.FirstOrder

/-- The relation symbols of `ℒ_Ad`: the binary `∈` and the unary `Ad`. -/
inductive AdRel : ℕ → Type
  | mem : AdRel 2
  | ad : AdRel 1

/-- **`ℒ_Ad`** (B92 §1): no function symbols; relation symbols `∈` and `Ad`. -/
abbrev LAd : Language where
  Func := fun _ => Empty
  Rel := AdRel

instance (k : ℕ) : DecidableEq (AdRel k) := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl

instance (k : ℕ) : Encodable (AdRel k) where
  encode := fun r => match k, r with
    | 2, AdRel.mem => 0
    | 1, AdRel.ad => 0
  decode := fun e => match k, e with
    | 2, 0 => some AdRel.mem
    | 1, 0 => some AdRel.ad
    | _, _ => none
  encodek := fun r => by cases r <;> rfl

instance : LAd.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

instance : LAd.Encodable := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

/-- `∈` as a distinguished symbol, so Foundation's `Operator.Mem` machinery applies. -/
instance : Language.Mem LAd := ⟨AdRel.mem⟩

variable {ξ : Type*} {n : ℕ}

/-! ### Atoms -/

/-- `s ∈ t`. -/
def memAt (s t : Semiterm LAd ξ n) : Semiformula LAd ξ n := Semiformula.rel AdRel.mem ![s, t]

/-- `s ∉ t` (that is, `¬(s ∈ t)`). -/
def nmemAt (s t : Semiterm LAd ξ n) : Semiformula LAd ξ n := Semiformula.nrel AdRel.mem ![s, t]

/-- `Ad(t)`. -/
def adAt (t : Semiterm LAd ξ n) : Semiformula LAd ξ n := Semiformula.rel AdRel.ad ![t]

/-- `¬Ad(t)`. -/
def nadAt (t : Semiterm LAd ξ n) : Semiformula LAd ξ n := Semiformula.nrel AdRel.ad ![t]

@[simp] theorem neg_memAt (s t : Semiterm LAd ξ n) : ∼(memAt s t) = nmemAt s t := rfl
@[simp] theorem neg_nmemAt (s t : Semiterm LAd ξ n) : ∼(nmemAt s t) = memAt s t := rfl
@[simp] theorem neg_adAt (t : Semiterm LAd ξ n) : ∼(adAt t) = nadAt t := rfl
@[simp] theorem neg_nadAt (t : Semiterm LAd ξ n) : ∼(nadAt t) = adAt t := rfl

/-- `memAt` is Foundation's `∈` operator. -/
theorem memAt_eq_operator (s t : Semiterm LAd ξ n) :
    memAt s t = Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![s, t] := by
  rw [Semiformula.Operator.mem_def]; rfl

/-! ### Restricted (bounded) quantifiers -/

/-- **`∀x∈t φ`** := `∀x (x ∈ t → φ)`.  In the body `φ` (one binder deeper) the bounding term is
`Rew.bShift t`, so `x ≢ t` (B92 p.3) holds by construction. -/
def ballAt (t : Semiterm LAd ξ n) (φ : Semiformula LAd ξ (n + 1)) : Semiformula LAd ξ n :=
  ∀¹ (nmemAt #0 (Rew.bShift t) ⋎ φ)

/-- **`∃x∈t φ`** := `∃x (x ∈ t ∧ φ)`. -/
def bexAt (t : Semiterm LAd ξ n) (φ : Semiformula LAd ξ (n + 1)) : Semiformula LAd ξ n :=
  ∃¹ (memAt #0 (Rew.bShift t) ⋏ φ)

@[simp] theorem neg_ballAt (t : Semiterm LAd ξ n) (φ : Semiformula LAd ξ (n + 1)) :
    ∼(ballAt t φ) = bexAt t (∼φ) := rfl

@[simp] theorem neg_bexAt (t : Semiterm LAd ξ n) (φ : Semiformula LAd ξ (n + 1)) :
    ∼(bexAt t φ) = ballAt t (∼φ) := rfl

/-- `ballAt` is Foundation's `ballMem`. -/
theorem ballAt_eq_ballMem (t : Semiterm LAd ξ n) (φ : Semiformula LAd ξ (n + 1)) :
    ballAt t φ = Semiformula.ballMem t φ := by
  simp [ballAt, Semiformula.ballMem, Semiformula.Operator.mem_def, nmemAt]
  rfl

/-- `bexAt` is Foundation's `bexsMem`. -/
theorem bexAt_eq_bexsMem (t : Semiterm LAd ξ n) (φ : Semiformula LAd ξ (n + 1)) :
    bexAt t φ = Semiformula.bexsMem t φ := by
  simp [bexAt, Semiformula.bexsMem, Semiformula.Operator.mem_def, memAt]
  rfl

/-! ### B92's abbreviations (p.3) -/

/-- `u ⊆ v` := `∀x∈u (x ∈ v)`. -/
def subsetAt (u v : Semiterm LAd ξ n) : Semiformula LAd ξ n := ballAt u (memAt #0 (Rew.bShift v))

/-- `u = v` := `u ⊆ v ∧ v ⊆ u`.  (B92 has no primitive equality.) -/
def eqAt (u v : Semiterm LAd ξ n) : Semiformula LAd ξ n := subsetAt u v ⋏ subsetAt v u

/-- `tran(u)` := `∀x∈u ∀y∈x (y ∈ u)`. -/
def tranAt (u : Semiterm LAd ξ n) : Semiformula LAd ξ n :=
  ballAt u (ballAt #0 (memAt #0 (Rew.bShift (Rew.bShift u))))

/-- `infinite(u)` := `∃x∈u (x ⊆ x) ∧ ∀x∈u ∃y∈u (x ∈ y)`, transcribed VERBATIM from B92 p.3
(the first conjunct is, as printed, trivially "`u` is nonempty"). -/
def infiniteAt (u : Semiterm LAd ξ n) : Semiformula LAd ξ n :=
  bexAt u (subsetAt #0 #0) ⋏ ballAt u (bexAt (Rew.bShift u) (memAt #1 #0))

end KPi

end OrdinalAnalysis
