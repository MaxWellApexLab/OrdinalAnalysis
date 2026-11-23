/-
  The list-sequent one-sided second-order LK used throughout the ACA / ACA_omega development,
  and its bridge to Foundation's multiset calculus.

  Provenance: this file is written here from scratch.  Foundation
  no longer ships a list-sequent second-order calculus -- its `FFL.SecondOrder.LK` works with
  `Multiset` sequents.  What is
  written below is the textbook one-sided system for second-order arithmetic syntax
  (identity, cut, weakening by inclusion, verum, and, or, first-order and set quantifiers
  with eigenvariable resp. witness), with the sequent operations (`shift₀`, `shift₁`, `∼`) the
  rest of the development uses, all on lists, exactly as before the Foundation migration.

  Contact with Foundation: the syntax (`Proposition`, `Semiproposition`, `free₀`, `free₁`,
  `shift₀`, `shift₁`, `∃²` substitution) and, for the bridge in section 3 only, the public
  API of `FFL.SecondOrder.LK.Derivation` (its constructors and the structural-subset
  derived rule `Structural.ofSubset`).  No Foundation source text is copied.

  The names live in `FFL.SecondOrder` so that the existing sources, which `open FFL` and say
  `SecondOrder.Sequent` / `SecondOrder.Sequent.shift₁` / `SecondOrder.Derivation`, resolve
  unchanged.
-/

module

public import Foundation.SecondOrder.LK.Basic

@[expose] public section

set_option autoImplicit false

namespace FFL.SecondOrder

open FirstOrder

variable {L : Language}

/-! ## Sequents as lists -/

/-- A second-order one-sided sequent: a finite list of propositions. -/
abbrev Sequent (L : Language) := List (Proposition L)

namespace Sequent

/-- Shift the free first-order variables of every member. -/
def shift₀ (Γ : Sequent L) : Sequent L := Γ.map Semiproposition.shift₀

@[simp] lemma shift₀_nil : shift₀ ([] : Sequent L) = [] := rfl

@[simp] lemma shift₀_cons (φ : Proposition L) (Γ : Sequent L) :
    shift₀ (φ :: Γ) = Semiproposition.shift₀ φ :: shift₀ Γ := rfl

@[simp] lemma shift₀_append (Γ Δ : Sequent L) : shift₀ (Γ ++ Δ) = shift₀ Γ ++ shift₀ Δ :=
  List.map_append

/-- Shift the free set variables of every member. -/
def shift₁ (Γ : Sequent L) : Sequent L := Γ.map Semiproposition.shift₁

@[simp] lemma shift₁_nil : shift₁ ([] : Sequent L) = [] := rfl

@[simp] lemma shift₁_cons (φ : Proposition L) (Γ : Sequent L) :
    shift₁ (φ :: Γ) = Semiproposition.shift₁ φ :: shift₁ Γ := rfl

@[simp] lemma shift₁_append (Γ Δ : Sequent L) : shift₁ (Γ ++ Δ) = shift₁ Γ ++ shift₁ Δ :=
  List.map_append

@[simp] lemma tilde_nil : ∼([] : Sequent L) = [] := rfl

@[simp] lemma tilde_cons (φ : Proposition L) (Γ : Sequent L) :
    ∼(φ :: Γ) = ∼φ :: ∼Γ := rfl

end Sequent

/-! ## The calculus -/

/-- Second-order one-sided LK on list sequents.  `wk` is the structural rule in its strongest
form: from a derivation of `Γ` get one of every `Δ ⊇ Γ`.  Note that `exs₂` instantiates a set
quantifier by an arbitrary formula (full comprehension). -/
inductive Derivation : Sequent L → Type
  | identity {φ : Proposition L} : Derivation [φ, ∼φ]
  | cut {φ : Proposition L} {Γ : Sequent L} :
      Derivation (φ :: Γ) → Derivation (∼φ :: Γ) → Derivation Γ
  | wk {Γ Δ : Sequent L} : Derivation Γ → Γ ⊆ Δ → Derivation Δ
  | verum : Derivation [⊤]
  | and {φ ψ : Proposition L} {Γ : Sequent L} :
      Derivation (φ :: Γ) → Derivation (ψ :: Γ) → Derivation (φ ⋏ ψ :: Γ)
  | or {φ ψ : Proposition L} {Γ : Sequent L} :
      Derivation (φ :: ψ :: Γ) → Derivation (φ ⋎ ψ :: Γ)
  | all₁ {φ : Semiproposition L 0 1} {Γ : Sequent L} :
      Derivation (φ.free₀ :: Sequent.shift₀ Γ) → Derivation ((∀¹ φ) :: Γ)
  | exs₁ {φ : Semiproposition L 0 1} {t : Semiterm L ℕ 0} {Γ : Sequent L} :
      Derivation (φ/[t] :: Γ) → Derivation ((∃¹ φ) :: Γ)
  | all₂ {φ : Semiproposition L 1 0} {Γ : Sequent L} :
      Derivation (φ.free₁ :: Sequent.shift₁ Γ) → Derivation ((∀² φ) :: Γ)
  | exs₂ {φ : Semiproposition L 1 0} {ψ : Semiproposition L 0 1} {Γ : Sequent L} :
      Derivation (φ/⟦ψ⟧ :: Γ) → Derivation ((∃² φ) :: Γ)

namespace Derivation

/-- Transport along an equality of end sequents. -/
def cast {Γ Δ : Sequent L} (d : Derivation Γ) (h : Γ = Δ) : Derivation Δ := h ▸ d

end Derivation

/-! ## Bridge to Foundation's multiset calculus

Every list derivation is a multiset derivation of the coerced end sequent. -/

namespace ListLK

lemma coe_cons (φ : Proposition L) (Γ : Sequent L) :
    ((φ :: Γ : Sequent L) : LK.Sequent L) = (Γ : LK.Sequent L) + ⦃φ⦄ := by
  rw [← Multiset.cons_coe, Multiset.atom_eq_singleton, add_comm, Multiset.singleton_add]

lemma coe_append (Γ Δ : Sequent L) :
    ((Γ ++ Δ : Sequent L) : LK.Sequent L) = (Γ : LK.Sequent L) + (Δ : LK.Sequent L) :=
  Multiset.coe_add _ _ |>.symm

lemma coe_nil : (([] : Sequent L) : LK.Sequent L) = 0 := rfl

lemma coe_single (φ : Proposition L) : (([φ] : Sequent L) : LK.Sequent L) = ⦃φ⦄ := by
  rw [coe_cons, coe_nil, zero_add]

lemma coe_pair (φ ψ : Proposition L) :
    (([φ, ψ] : Sequent L) : LK.Sequent L) = ⦃φ, ψ⦄ := by
  rw [coe_cons, coe_cons, coe_nil]
  show (0 : LK.Sequent L) + ⦃ψ⦄ + ⦃φ⦄ = ⦃φ, ψ⦄
  rw [zero_add, add_comm]

lemma coe_cons2 (φ ψ : Proposition L) (Γ : Sequent L) :
    ((φ :: ψ :: Γ : Sequent L) : LK.Sequent L) = (Γ : LK.Sequent L) + ⦃φ, ψ⦄ := by
  rw [coe_cons, coe_cons, add_assoc]
  congr 1
  rw [add_comm]

lemma coe_shift₀ (Γ : Sequent L) :
    ((Sequent.shift₀ Γ : Sequent L) : LK.Sequent L) = LK.Sequent.shift₀ (Γ : LK.Sequent L) := by
  simp [Sequent.shift₀, LK.Sequent.shift₀]

lemma coe_shift₁ (Γ : Sequent L) :
    ((Sequent.shift₁ Γ : Sequent L) : LK.Sequent L) = LK.Sequent.shift₁ (Γ : LK.Sequent L) := by
  simp [Sequent.shift₁, LK.Sequent.shift₁]

end ListLK

open ListLK

/-- The multiset derivation underlying a list derivation. -/
noncomputable def Derivation.toMultiset :
    {Γ : Sequent L} → Derivation Γ → LK.Derivation (Γ : LK.Sequent L)
  | _, .identity => (LK.Derivation.identity).cast (coe_pair _ _).symm
  | _, .cut (Γ := Γ) dp dn => by
      classical
      refine Structural.ofSubset (F := Proposition L) (𝔇 := LK.Derivation (L := L))
        (Multiset.Traversal.ofList (Γ ++ Γ)) (Multiset.Traversal.ofList Γ)
        ((LK.Derivation.cut (dp.toMultiset.cast (coe_cons _ _))
          (dn.toMultiset.cast (coe_cons _ _))).cast (coe_append _ _).symm) ?_
      intro x hx
      simpa using hx
  | _, .wk (Γ := Γ) (Δ := Δ) d h => by
      classical
      exact Structural.ofSubset (F := Proposition L) (𝔇 := LK.Derivation (L := L))
        (Multiset.Traversal.ofList Γ) (Multiset.Traversal.ofList Δ) d.toMultiset
        (fun x hx ↦ by simpa using h (by simpa using hx))
  | _, .verum => (LK.Derivation.verum).cast (coe_single _).symm
  | _, .and dp dq =>
      (LK.Derivation.and (dp.toMultiset.cast (coe_cons _ _)) (dq.toMultiset.cast (coe_cons _ _))).cast
        (coe_cons _ _).symm
  | _, .or d =>
      (LK.Derivation.or (d.toMultiset.cast (coe_cons2 _ _ _))).cast (coe_cons _ _).symm
  | _, .all₁ (Γ := Γ) d =>
      (LK.Derivation.all₁ (Γ := (Γ : LK.Sequent L))
        (d.toMultiset.cast (by rw [coe_cons, coe_shift₀, add_comm]))).cast (coe_cons _ _).symm
  | _, .exs₁ d =>
      (LK.Derivation.exs₁ (d.toMultiset.cast (coe_cons _ _))).cast (coe_cons _ _).symm
  | _, .all₂ (Γ := Γ) d =>
      (LK.Derivation.all₂ (Γ := (Γ : LK.Sequent L))
        (d.toMultiset.cast (by rw [coe_cons, coe_shift₁, add_comm]))).cast (coe_cons _ _).symm
  | _, .exs₂ d =>
      (LK.Derivation.exs₂ (d.toMultiset.cast (coe_cons _ _))).cast (coe_cons _ _).symm

end FFL.SecondOrder
