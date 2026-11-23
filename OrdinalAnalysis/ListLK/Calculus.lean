/-
  The list-sequent one-sided LK calculus used throughout this development.

  Provenance: this file is written here from scratch.  Foundation
  no longer ships a list-sequent calculus -- its `FFL.FirstOrder.LK` works with
  `Multiset` sequents.  The
  calculus below is written from the textbook definition of the Tait/Schutte one-sided
  system (identity, cut, subset-contraction, verum, or, and, all with an eigenvariable,
  exists with a witness), and everything downstream of it (cut rank, elimination, the
  ordinal bounds) stays on lists, exactly as before the Foundation migration.

  Contact with Foundation happens only in `OrdinalAnalysis.ListLK.Bridge`, which uses
  Foundation's public API to transport statements across a list <-> multiset translation.

  The names live in `FFL.FirstOrder` so that the existing sources, which `open` that
  namespace and say `Sequent` / `Derivation` / `Γˡ⁺`, resolve unchanged.
-/

module

public import Foundation.FirstOrder.Syntax
public import Foundation.FirstOrder.Tarski
public import Foundation.FirstOrder.LK.Basic
public import Foundation.FirstOrder.LK.CutFree
public import Foundation.FirstOrder.LK.Soundness

@[expose] public section

set_option autoImplicit true

namespace FFL.FirstOrder

variable {L : Language}

/-! ## Sequents as lists, and the shift of all free variables -/

/-- A one-sided sequent: a finite list of propositions. -/
abbrev Sequent (L : Language) := List (Proposition L)

/-- Shift the free variables of every member of a list. -/
def Rewriting.lshifts {F : ℕ → Type*} {n : ℕ} [LCWQ F] [Rewriting L ℕ F ℕ F]
    (Γ : List (F n)) : List (F n) := List.map Rewriting.shift Γ

@[inherit_doc] postfix:max "ˡ⁺" => Rewriting.lshifts

namespace Rewriting

variable {F : ℕ → Type*} {n : ℕ} [LCWQ F] [Rewriting L ℕ F ℕ F]

@[simp] lemma lshifts_nil : ([] : List (F n))ˡ⁺ = [] := rfl

@[simp] lemma lshifts_cons (φ : F n) (Γ : List (F n)) :
    (φ :: Γ)ˡ⁺ = shift φ :: Γˡ⁺ := rfl

@[simp] lemma lshifts_append (Γ Δ : List (F n)) : (Γ ++ Δ)ˡ⁺ = Γˡ⁺ ++ Δˡ⁺ :=
  List.map_append

@[simp] lemma lshifts_neg (Γ : List (F n)) : (∼Γ)ˡ⁺ = ∼(Γˡ⁺) := by
  induction Γ with
  | nil => rfl
  | cons a Γ ih => simp [List.tilde_def, ih]

@[simp] lemma mem_lshifts_iff' {φ : F n} {Γ : List (F n)} :
    φ ∈ Γˡ⁺ ↔ ∃ ψ ∈ Γ, shift ψ = φ := List.mem_map

lemma lshifts_subset {Γ Δ : List (F n)} (h : Γ ⊆ Δ) : Γˡ⁺ ⊆ Δˡ⁺ :=
  List.map_subset _ h

end Rewriting

namespace LawfulSyntacticRewriting

variable {n : ℕ} {S : ℕ → Type*} [LCWQ S] [SyntacticRewriting L S S] [LawfulSyntacticRewriting L S]

@[simp] lemma mem_lshifts_iff {φ : S n} {Γ : List (S n)} :
    Rewriting.shift φ ∈ Γˡ⁺ ↔ φ ∈ Γ := by
  rw [Rewriting.mem_lshifts_iff']
  exact ⟨fun ⟨ψ, hψ, e⟩ ↦ shift_injective e ▸ hψ, fun h ↦ ⟨φ, h, rfl⟩⟩

@[simp] lemma lshifts_ss (Γ Δ : List (S n)) : Γˡ⁺ ⊆ Δˡ⁺ ↔ Γ ⊆ Δ :=
  ⟨fun h _ hx ↦ mem_lshifts_iff.mp (h (mem_lshifts_iff.mpr hx)), Rewriting.lshifts_subset⟩

end LawfulSyntacticRewriting

namespace Sequent

/-- The sentences of a list, read as propositions. -/
def embed (Γ : List (Sentence L)) : Sequent L := Γ.map Rewriting.emb

@[simp] lemma embed_nil : embed ([] : List (Sentence L)) = [] := rfl

@[simp] lemma embed_cons {φ : Sentence L} {Γ : List (Sentence L)} :
    embed (φ :: Γ) = (↑φ :: embed Γ) := rfl

@[simp] lemma embed_append (Γ Δ : List (Sentence L)) :
    embed (Γ ++ Δ) = embed Γ ++ embed Δ := List.map_append

@[simp] lemma embed_shift (Γ : List (Sentence L)) : (embed Γ)ˡ⁺ = embed Γ := by
  induction Γ with
  | nil => rfl
  | cons a Γ ih => simp [ih]

end Sequent

/-! ## The calculus -/

/-- Derivations of one-sided sequents given as lists.  `contraction` is the structural rule
in its strongest form: from a derivation of `Δ` get one of every `Γ ⊇ Δ`. -/
inductive Derivation : Sequent L → Type _
  | identity (r : L.Rel k) (v) : Derivation [.rel r v, .nrel r v]
  | cut : Derivation (φ :: Γ) → Derivation (∼φ :: Δ) → Derivation (Γ ++ Δ)
  | contraction : Derivation Δ → Δ ⊆ Γ → Derivation Γ
  | verum : Derivation [⊤]
  | or : Derivation (φ :: ψ :: Γ) → Derivation (φ ⋎ ψ :: Γ)
  | and : Derivation (φ :: Γ) → Derivation (ψ :: Γ) → Derivation (φ ⋏ ψ :: Γ)
  | all : Derivation (φ.free :: Γˡ⁺) → Derivation ((∀¹ φ) :: Γ)
  | exs : Derivation (φ/[t] :: Γ) → Derivation ((∃¹ φ) :: Γ)

prefix:45 "⊢ᶠ¹ " => Derivation

namespace Derivation

/-- Number of inference rules on the longest branch. -/
def height : {Δ : Sequent L} → ⊢ᶠ¹ Δ → ℕ
  | _, identity _ _ => 0
  | _, cut dp dn => max dp.height dn.height + 1
  | _, contraction d _ => d.height + 1
  | _, verum => 0
  | _, or d => d.height + 1
  | _, and dp dq => max dp.height dq.height + 1
  | _, all d => d.height + 1
  | _, exs d => d.height + 1

@[simp] lemma height_identity {k} {r : L.Rel k} {v} : height (identity r v) = 0 := rfl

@[simp] lemma height_cut {φ} {Γ Δ : Sequent L} (dp : ⊢ᶠ¹ φ :: Γ) (dn : ⊢ᶠ¹ ∼φ :: Δ) :
    height (cut dp dn) = (max (height dp) (height dn)).succ := rfl

@[simp] lemma height_contraction {Δ Γ : Sequent L} (d : ⊢ᶠ¹ Δ) (h : Δ ⊆ Γ) :
    height (contraction d h) = d.height.succ := rfl

@[simp] lemma height_verum : height (verum : ⊢ᶠ¹ ([⊤] : Sequent L)) = 0 := rfl

@[simp] lemma height_and {φ ψ} {Γ : Sequent L} (dp : ⊢ᶠ¹ φ :: Γ) (dq : ⊢ᶠ¹ ψ :: Γ) :
    height (and dp dq) = (max (height dp) (height dq)).succ := rfl

@[simp] lemma height_or {φ ψ} {Γ : Sequent L} (d : ⊢ᶠ¹ φ :: ψ :: Γ) :
    height (or d) = d.height.succ := rfl

@[simp] lemma height_all {φ : Semiproposition L 1} {Γ : Sequent L} (d : ⊢ᶠ¹ φ.free :: Γˡ⁺) :
    height (all d) = d.height.succ := rfl

@[simp] lemma height_exs {t} {φ} {Γ : Sequent L} (d : ⊢ᶠ¹ φ/[t] :: Γ) :
    height (exs d) = d.height.succ := rfl

/-- Transport along an equality of end sequents. -/
protected abbrev cast {Δ Γ : Sequent L} (d : ⊢ᶠ¹ Δ) (e : Δ = Γ := by simp) : ⊢ᶠ¹ Γ := e ▸ d

@[simp] lemma height_cast {Δ Γ : Sequent L} (d : ⊢ᶠ¹ Δ) (e : Δ = Γ) :
    height (Derivation.cast d e) = height d := by
  subst e; rfl

/-! ### Cut-free derivations -/

/-- No `cut` rule occurs anywhere in the derivation. -/
inductive IsCutFree : {Γ : Sequent L} → ⊢ᶠ¹ Γ → Prop
  | identity (r : L.Rel k) (v) : IsCutFree (identity r v)
  | verum : IsCutFree verum
  | or {d : ⊢ᶠ¹ φ :: ψ :: Γ} : IsCutFree d → IsCutFree d.or
  | and {dφ : ⊢ᶠ¹ φ :: Γ} {dψ : ⊢ᶠ¹ ψ :: Γ} : IsCutFree dφ → IsCutFree dψ →
      IsCutFree (dφ.and dψ)
  | all {d : ⊢ᶠ¹ Rewriting.free φ :: Γˡ⁺} : IsCutFree d → IsCutFree d.all
  | exs (t) {d : ⊢ᶠ¹ φ/[t] :: Γ} : IsCutFree d → IsCutFree d.exs
  | contraction {d : ⊢ᶠ¹ Δ} (ss : Δ ⊆ Γ) : IsCutFree d → IsCutFree (d.contraction ss)

attribute [simp] IsCutFree.identity IsCutFree.verum

section isCutFree

variable {Γ Δ : Sequent L}

@[simp] lemma isCutFree_or_iff {d : ⊢ᶠ¹ φ :: ψ :: Γ} : IsCutFree d.or ↔ IsCutFree d :=
  ⟨fun h ↦ by cases h; assumption, .or⟩

@[simp] lemma isCutFree_and_iff {dφ : ⊢ᶠ¹ φ :: Γ} {dψ : ⊢ᶠ¹ ψ :: Γ} :
    IsCutFree (dφ.and dψ) ↔ IsCutFree dφ ∧ IsCutFree dψ :=
  ⟨fun h ↦ by cases h; exact ⟨‹_›, ‹_›⟩, fun h ↦ h.1.and h.2⟩

@[simp] lemma isCutFree_all_iff {d : ⊢ᶠ¹ Rewriting.free φ :: Γˡ⁺} :
    IsCutFree d.all ↔ IsCutFree d := ⟨fun h ↦ by cases h; assumption, .all⟩

@[simp] lemma isCutFree_exs_iff {d : ⊢ᶠ¹ φ/[t] :: Γ} : IsCutFree d.exs ↔ IsCutFree d :=
  ⟨fun h ↦ by cases h; assumption, .exs t⟩

@[simp] lemma isCutFree_contraction_iff {d : ⊢ᶠ¹ Δ} {ss : Δ ⊆ Γ} :
    IsCutFree (d.contraction ss) ↔ IsCutFree d :=
  ⟨fun h ↦ by cases h; assumption, .contraction _⟩

@[simp] lemma IsCutFree.cast {d : ⊢ᶠ¹ Γ} {e : Γ = Δ} :
    IsCutFree (Derivation.cast d e) ↔ IsCutFree d := by subst e; rfl

@[simp] lemma IsCutFree.not_cut (dp : ⊢ᶠ¹ φ :: Γ) (dn : ⊢ᶠ¹ ∼φ :: Δ) :
    ¬IsCutFree (dp.cut dn) := fun h ↦ by
  refine h.rec (motive := fun {_} d _ ↦ match d with | .cut _ _ => False | _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp

end isCutFree

end Derivation

end FFL.FirstOrder
