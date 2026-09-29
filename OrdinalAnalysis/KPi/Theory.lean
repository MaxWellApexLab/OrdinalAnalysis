/-
  The theory `KPi` (Buchholz 1992, §2, "Axioms of KPi", PDF p.8-9): Kripke-Platek set theory with
  an unbounded chain of admissible sets, in the language `ℒ_Ad` (`∈` and `Ad`).

  B92's list, transcribed (with B92's defined `=`, `⊆`, `tran`, `infinite` from `Language.lean`):

    (Ext)    ∀x∀y∀z [x = y → (x ∈ z → y ∈ z) ∧ (Ad(x) → Ad(y))]
    (Found)  ∀z⃗ [∀x(∀y∈x φ(y,z⃗) → φ(x,z⃗)) → ∀x φ(x,z⃗)]                         (φ any ℒ_Ad-formula)
    (Pair)   ∀x∀y∃z (x ∈ z ∧ y ∈ z)
    (Union)  ∀x∃z ∀y∈x ∀u∈y (u ∈ z)
    (Δ₀-Sep) ∀z⃗∀w∃y [∀x∈y (x ∈ w ∧ φ(x,z⃗)) ∧ ∀x∈w (φ(x,z⃗) → x ∈ y)]              (φ ∈ Δ₀)
    (Δ₀-Col) ∀z⃗∀w [∀x∈w ∃y φ(x,y,z⃗) → ∃w₁ ∀x∈w ∃y∈w₁ φ(x,y,z⃗)]                  (φ ∈ Δ₀)
    (Ad.1)   ∀x [Ad(x) → tran(x) ∧ ∃w∈x infinite(w)]
    (Ad.2)   ∀x∀y [Ad(x) ∧ Ad(y) → (x ∈ y ∨ x = y ∨ y ∈ x)]
    (Ad.3)   ∀x [Ad(x) → ψ^x],   for every instance ψ of (Pair), (Union), (Δ₀-Sep), (Δ₀-Col)
    (Lim)    ∀x∃y (Ad(y) ∧ x ∈ y)

  **Schema conventions** (fixed once; `SlotCheck.lean` checks them against Foundation's own quote
  notation and against direct semantics).

    * A schema formula is a `Semiformula LAd ℕ k`: the schematic variables `x` (and `y`) are the
      bound variables `#0` (and `#1`) — *first argument = `#0`*, exactly Foundation's convention
      for `!φ x y` — and the parameters `z⃗` are the free variables `&0, &1, …`.  The axiom is the
      universal closure `Semiformula.univCl` over those free variables (all `&i`, `i < fvSup`).
      The bound variables `w`, `y`/`w₁` of the axiom itself are bound *inside* the schema body and
      are therefore unreachable from `φ` (B92: `φ`'s free variables are among `x, z⃗`).
    * Instantiation of a schema formula at actual variables is `Rew.subst` (`φ ⇜ ![a, b]`,
      `#0 := a`, `#1 := b`).
    * `Ad.3` is over instances of the four axioms *as sentences*, i.e. after the parameter
      closure; `relAt` (Delta0.lean) relativises only the unrestricted quantifiers, so the
      `Δ₀` matrix of `Sep`/`Col` is untouched, exactly as in B92.
    * Full `Found` is included (all ℒ_Ad-formulas, `Ad` atoms allowed); it is *not* restricted
      to Δ₀ or to closed instances — B92 has full foundation (KPi with full Foundation), and the
      `(Found)*` rule of RS* (B92 Def 2.2) corresponds to it.

  **NOTHING may be built on `KPi` until a soundness theorem (a model of `KPi`) exists** — project
  rule; see the soundness proposal in the design notes.  This file contains
  definitions and membership lemmas only.

  Contents.

    `extAx`, `foundAx`, `pairAx`, `unionAx`, `sepAx`, `colAx`, `ad1Ax`, `ad2Ax`, `ad3Ax`, `limAx`
    `Ad3Base`                     the instances `ψ` over which `Ad.3` ranges
    `KPi`                         the theory (one constructor per axiom / schema)
-/
import OrdinalAnalysis.KPi.Delta0

set_option autoImplicit false
set_option linter.dupNamespace false

namespace OrdinalAnalysis

namespace KPi

open LO LO.FirstOrder

/-! ### The individual axioms and schema bodies -/

/-- **(Ext)** `∀x∀y∀z [x = y → (x ∈ z → y ∈ z) ∧ (Ad(x) → Ad(y))]`, with `=` defined as
`⊆ ∧ ⊇`.  In `∀¹ ∀¹ ∀¹`: `x = #2`, `y = #1`, `z = #0`. -/
def extAx : Sentence LAd :=
  ∀¹ (∀¹ (∀¹ (eqAt #2 #1 🡒 ((memAt #2 #0 🡒 memAt #1 #0) ⋏ (adAt #2 🡒 adAt #1)))))

/-- The body of **(Found)** for `φ(x, z⃗)` (`x = #0`, `z⃗ = &i`):
`∀x(∀y∈x φ(y,z⃗) → φ(x,z⃗)) → ∀x φ(x,z⃗)`.  Inside `∀x` (context `x = #0`), `∀y∈x` has body
context `y = #0, x = #1`, where `φ(y)` is `φ/[#0]`. -/
def foundBody (φ : Semiformula LAd ℕ 1) : Proposition LAd :=
  (∀¹ (ballAt #0 (φ/[#0]) 🡒 φ)) 🡒 ∀¹ φ

/-- **(Found)** instance at `φ`: the universal closure of `foundBody φ` over the parameters. -/
def foundAx (φ : Semiformula LAd ℕ 1) : Sentence LAd := (foundBody φ).univCl

/-- **(Pair)** `∀x∀y∃z (x ∈ z ∧ y ∈ z)`: `x = #2`, `y = #1`, `z = #0`. -/
def pairAx : Sentence LAd :=
  ∀¹ (∀¹ (∃¹ (memAt #2 #0 ⋏ memAt #1 #0)))

/-- **(Union)** `∀x∃z ∀y∈x ∀u∈y (u ∈ z)`: after `∀x ∃z`, `x = #1`, `z = #0`; in `∀y∈x` the body
context is `y = #0, z = #1, x = #2`; in `∀u∈y` it is `u = #0, y = #1, z = #2`. -/
def unionAx : Sentence LAd :=
  ∀¹ (∃¹ (ballAt #1 (ballAt #0 (memAt #0 #2))))

/-- The matrix of **(Δ₀-Sep)**, in the context `w = #1`, `y = #0`:
`∀x∈y (x ∈ w ∧ φ(x,z⃗)) ∧ ∀x∈w (φ(x,z⃗) → x ∈ y)`. -/
def sepMat (φ : Semiformula LAd ℕ 1) : Semiformula LAd ℕ 2 :=
  ballAt #0 (memAt #0 #2 ⋏ φ/[#0]) ⋏ ballAt #1 (φ/[#0] 🡒 memAt #0 #1)

/-- The body of **(Δ₀-Sep)** for `φ(x, z⃗)`:
`∀w∃y [∀x∈y (x ∈ w ∧ φ(x,z⃗)) ∧ ∀x∈w (φ(x,z⃗) → x ∈ y)]`.
After `∀w ∃y`: `w = #1`, `y = #0`.  Both `∀x∈·` bodies have context `x = #0, y = #1, w = #2`. -/
def sepBody (φ : Semiformula LAd ℕ 1) : Proposition LAd :=
  ∀¹ (∃¹ (sepMat φ))

/-- **(Δ₀-Sep)** instance at `φ` (intended: `φ ∈ Δ₀`; the hypothesis is carried by `KPi.sep`). -/
def sepAx (φ : Semiformula LAd ℕ 1) : Sentence LAd := (sepBody φ).univCl

/-- The body of **(Δ₀-Col)** for `φ(x, y, z⃗)` (`x = #0`, `y = #1` in `φ`'s own numbering):
`∀w [∀x∈w ∃y φ(x,y,z⃗) → ∃w₁ ∀x∈w ∃y∈w₁ φ(x,y,z⃗)]`.
After `∀w`: `w = #0`.  Antecedent: `∀x∈w` body context `x = #0, w = #1`; `∃y` body context
`y = #0, x = #1, w = #2`.  Consequent: after `∃w₁`: `w₁ = #0, w = #1`; `∀x∈w` body context
`x = #0, w₁ = #1, w = #2`; `∃y∈w₁` body context `y = #0, x = #1, w₁ = #2, w = #3`.  In both
matrices the actual `(x, y)` sit at `(#1, #0)`, hence `φ ⇜ ![#1, #0]`. -/
def colBody (φ : Semiformula LAd ℕ 2) : Proposition LAd :=
  ∀¹ (ballAt #0 (∃¹ (φ ⇜ ![#1, #0])) 🡒 ∃¹ (ballAt #1 (bexAt #1 (φ ⇜ ![#1, #0]))))

/-- **(Δ₀-Col)** instance at `φ` (intended: `φ ∈ Δ₀`; the hypothesis is carried by `KPi.col`). -/
def colAx (φ : Semiformula LAd ℕ 2) : Sentence LAd := (colBody φ).univCl

/-- **(Ad.1)** `∀x [Ad(x) → tran(x) ∧ ∃w∈x infinite(w)]`. -/
def ad1Ax : Sentence LAd :=
  ∀¹ (adAt #0 🡒 (tranAt #0 ⋏ bexAt #0 (infiniteAt #0)))

/-- **(Ad.2)** `∀x∀y [Ad(x) ∧ Ad(y) → (x ∈ y ∨ x = y ∨ y ∈ x)]`: `x = #1`, `y = #0`. -/
def ad2Ax : Sentence LAd :=
  ∀¹ (∀¹ ((adAt #1 ⋏ adAt #0) 🡒 (memAt #1 #0 ⋎ (eqAt #1 #0 ⋎ memAt #0 #1))))

/-- **(Ad.3)** at the sentence `ψ`: `∀x [Ad(x) → ψ^x]`.  `ψ` is weakened to one free bound
variable (`Rew.bShift ▹ ψ`; a sentence mentions none) and relativised to `x = #0`. -/
def ad3Ax (ψ : Sentence LAd) : Sentence LAd :=
  ∀¹ (adAt #0 🡒 relAt #0 (Rew.bShift ▹ ψ))

/-- **(Lim)** `∀x∃y (Ad(y) ∧ x ∈ y)`: `x = #1`, `y = #0`. -/
def limAx : Sentence LAd :=
  ∀¹ (∃¹ (adAt #0 ⋏ memAt #1 #0))

/-! ### The theory -/

/-- The sentences `ψ` over which (Ad.3) ranges: "every instance `ψ` of (Pair), (Union),
(Δ₀-Sep), (Δ₀-Col)" (B92 p.9). -/
inductive Ad3Base : Sentence LAd → Prop
  | pair : Ad3Base pairAx
  | union : Ad3Base unionAx
  | sep (φ : Semiformula LAd ℕ 1) : IsDelta0 φ → Ad3Base (sepAx φ)
  | col (φ : Semiformula LAd ℕ 2) : IsDelta0 φ → Ad3Base (colAx φ)

/-- **`KPi`** (B92 §2): the theory in `ℒ_Ad` with the axioms (Ext), (Found), (Pair), (Union),
(Δ₀-Sep), (Δ₀-Col), (Ad.1), (Ad.2), (Ad.3), (Lim).  There is no primitive equality (`ℒ_Ad` has
none), hence no equality axioms: (Ext) makes the defined `=` a congruence. -/
inductive KPi : Theory LAd
  /-- (Ext) -/
  | ext : KPi extAx
  /-- (Found), all `ℒ_Ad`-formulas `φ(x, z⃗)` -/
  | found (φ : Semiformula LAd ℕ 1) : KPi (foundAx φ)
  /-- (Pair) -/
  | pair : KPi pairAx
  /-- (Union) -/
  | union : KPi unionAx
  /-- (Δ₀-Sep) -/
  | sep (φ : Semiformula LAd ℕ 1) (h : IsDelta0 φ) : KPi (sepAx φ)
  /-- (Δ₀-Col) -/
  | col (φ : Semiformula LAd ℕ 2) (h : IsDelta0 φ) : KPi (colAx φ)
  /-- (Ad.1) -/
  | ad1 : KPi ad1Ax
  /-- (Ad.2) -/
  | ad2 : KPi ad2Ax
  /-- (Ad.3), for every instance `ψ` of (Pair), (Union), (Δ₀-Sep), (Δ₀-Col) -/
  | ad3 {ψ : Sentence LAd} (h : Ad3Base ψ) : KPi (ad3Ax ψ)
  /-- (Lim) -/
  | lim : KPi limAx

theorem KPi.ad3_pair : KPi (ad3Ax pairAx) := KPi.ad3 Ad3Base.pair

theorem KPi.ad3_union : KPi (ad3Ax unionAx) := KPi.ad3 Ad3Base.union

theorem KPi.ad3_sep (φ : Semiformula LAd ℕ 1) (h : IsDelta0 φ) : KPi (ad3Ax (sepAx φ)) :=
  KPi.ad3 (Ad3Base.sep φ h)

theorem KPi.ad3_col (φ : Semiformula LAd ℕ 2) (h : IsDelta0 φ) : KPi (ad3Ax (colAx φ)) :=
  KPi.ad3 (Ad3Base.col φ h)

end KPi

end OrdinalAnalysis
