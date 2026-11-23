/-
  Bridge between our list-sequent calculus (`OrdinalAnalysis.ListLK.Calculus`) and the
  multiset calculus `FFL.FirstOrder.LK.Derivation` of Foundation.

  Provenance: OUR OWN text.  Only Foundation's public API is used (its derivation type with
  constructors, `LK.Derivation.cast`, `Structural.ofSubset`, `Multiset.Traversal.ofList`,
  `Canonical.hauptsatz`, `Theory.Proof.provable_iff`); no Foundation source text is copied.

  Route (the milestones of the original port):
    1. a list is a multiset (`coe_*` equations for `::`, `++`, shifts, `∼`, `embed`);
    2. `Derivation.toMultiset`: every list derivation is a multiset derivation of the coerced
       end sequent -- one clause per rule, `contraction` via Foundation's structural subset rule;
    3. `Derivation.ofMultiset`: every multiset derivation yields a list derivation of
       *any* list representing the same multiset -- by recursion on the multiset derivation,
       always closing with a subset-contraction that repairs the order of the list;
    4. consequences used by the development:
         `Theory.Proof.provable_iff_list`   provability from finitely many axioms, as a list derivation;
         `Derivation.Canonical.hauptsatz`   cut elimination for list derivations.
-/

module

public import OrdinalAnalysis.ListLK.Calculus
public import Foundation.FirstOrder.LK.Hauptsatz
public import Foundation.FirstOrder.LK.Completeness

@[expose] public section

set_option autoImplicit true

namespace FFL.FirstOrder

variable {L : Language}

/-! ### 1. Lists as multisets -/

namespace ListLK

lemma coe_cons (φ : Proposition L) (Γ : Sequent L) :
    ((φ :: Γ : Sequent L) : LK.Sequent L) = (Γ : LK.Sequent L) + ⦃φ⦄ := by
  rw [← Multiset.cons_coe, Multiset.atom_eq_singleton, add_comm, Multiset.singleton_add]

lemma coe_append (Γ Δ : Sequent L) :
    ((Γ ++ Δ : Sequent L) : LK.Sequent L) = (Γ : LK.Sequent L) + (Δ : LK.Sequent L) :=
  Multiset.coe_add _ _ |>.symm

lemma coe_lshifts (Γ : Sequent L) :
    ((Γˡ⁺ : Sequent L) : LK.Sequent L) = (Γ : LK.Sequent L)⁺ := by
  simp [Rewriting.lshifts, Rewriting.shifts]

lemma coe_tilde (Γ : Sequent L) :
    ((∼Γ : Sequent L) : LK.Sequent L) = ∼(Γ : LK.Sequent L) := by
  simp [List.tilde_def, Multiset.tilde_def]

lemma coe_embed (Γ : List (Sentence L)) :
    ((Sequent.embed Γ : Sequent L) : LK.Sequent L)
      = LK.Sequent.embed (Γ : Multiset (Sentence L)) := by
  simp [Sequent.embed, LK.Sequent.embed]

lemma coe_nil : (([] : Sequent L) : LK.Sequent L) = 0 := rfl

lemma coe_pair (φ ψ : Proposition L) :
    (([φ, ψ] : Sequent L) : LK.Sequent L) = ⦃φ, ψ⦄ := by
  rw [coe_cons, coe_cons, coe_nil]
  show (0 : LK.Sequent L) + ⦃ψ⦄ + ⦃φ⦄ = ⦃φ, ψ⦄
  rw [zero_add, add_comm]

lemma coe_single (φ : Proposition L) : (([φ] : Sequent L) : LK.Sequent L) = ⦃φ⦄ := by
  rw [coe_cons, coe_nil, zero_add]

lemma coe_cons2 (φ ψ : Proposition L) (Γ : Sequent L) :
    ((φ :: ψ :: Γ : Sequent L) : LK.Sequent L) = (Γ : LK.Sequent L) + ⦃φ, ψ⦄ := by
  rw [coe_cons, coe_cons, add_assoc]
  congr 1
  rw [add_comm]

end ListLK

open ListLK

/-! ### 2. List derivations are multiset derivations -/

/-- The multiset derivation underlying a list derivation. -/
noncomputable def Derivation.toMultiset :
    {Γ : Sequent L} → ⊢ᶠ¹ Γ → LK.Derivation (Γ : LK.Sequent L)
  | _, .identity r v => (LK.Derivation.identity r v).cast (coe_pair _ _).symm
  | _, .cut dp dn =>
      (LK.Derivation.cut (dp.toMultiset.cast (coe_cons _ _)) (dn.toMultiset.cast (coe_cons _ _))).cast
        (coe_append _ _).symm
  | _, .contraction (Δ := Δ) (Γ := Γ) d h => by
      classical
      exact Structural.ofSubset (F := Proposition L) (𝔇 := LK.Derivation (L := L))
        (Multiset.Traversal.ofList Δ) (Multiset.Traversal.ofList Γ) d.toMultiset
        (fun x hx ↦ by simpa using h (by simpa using hx))
  | _, .verum => (LK.Derivation.verum).cast (coe_single _).symm
  | _, .or d =>
      (LK.Derivation.or (d.toMultiset.cast (coe_cons2 _ _ _))).cast (coe_cons _ _).symm
  | _, .and dp dq =>
      (LK.Derivation.and (dp.toMultiset.cast (coe_cons _ _)) (dq.toMultiset.cast (coe_cons _ _))).cast
        (coe_cons _ _).symm
  | _, .all (Γ := Γ) d =>
      (LK.Derivation.all (Γ := (Γ : LK.Sequent L))
        (d.toMultiset.cast (by rw [coe_cons, coe_lshifts]))).cast (coe_cons _ _).symm
  | _, .exs d =>
      (LK.Derivation.exs (d.toMultiset.cast (coe_cons _ _))).cast (coe_cons _ _).symm

/-! ### 3. Multiset derivations are list derivations -/

/-- A list derivation of `l` is enough to get one of any `l'` with the same members. -/
def Derivation.congr {l l' : Sequent L} (d : ⊢ᶠ¹ l) (h : ∀ x, x ∈ l → x ∈ l') : ⊢ᶠ¹ l' :=
  d.contraction h

local macro "mem_tac" : tactic =>
  `(tactic| (intro x hx
             simp only [Multiset.mem_toList, Multiset.mem_add, Multiset.mem_atom_iff,
               Multiset.mem_map, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
               Rewriting.lshifts, List.mem_map, Rewriting.shifts] at hx ⊢
             aesop))

/-- Every multiset derivation gives a list derivation of the canonical list of its end sequent. -/
noncomputable def Derivation.ofMultiset :
    {Δ : LK.Sequent L} → LK.Derivation Δ → ⊢ᶠ¹ Δ.toList
  | _, .identity r v => (Derivation.identity r v).congr (by mem_tac)
  | _, .cut (φ := φ) (Γ := Γ) (Δ := Δ) dp dn =>
      ((ofMultiset dp |>.congr (l' := φ :: Γ.toList) (by mem_tac)).cut
        (ofMultiset dn |>.congr (l' := ∼φ :: Δ.toList) (by mem_tac))).congr (by mem_tac)
  | _, .contraction d => (ofMultiset d).congr (by mem_tac)
  | _, .weakening d => (ofMultiset d).congr (by mem_tac)
  | _, .verum => Derivation.verum.congr (by mem_tac)
  | _, .or (φ := φ) (ψ := ψ) (Γ := Γ) d =>
      ((ofMultiset d).congr (l' := φ :: ψ :: Γ.toList) (by mem_tac)).or.congr (by mem_tac)
  | _, .and (φ := φ) (ψ := ψ) (Γ := Γ) dp dq =>
      (((ofMultiset dp).congr (l' := φ :: Γ.toList) (by mem_tac)).and
        ((ofMultiset dq).congr (l' := ψ :: Γ.toList) (by mem_tac))).congr (by mem_tac)
  | _, .all (φ := φ) (Γ := Γ) d =>
      ((ofMultiset d).congr (l' := φ.free :: (Γ.toList)ˡ⁺) (by mem_tac)).all.congr (by mem_tac)
  | _, .exs (φ := φ) (Γ := Γ) (t := t) d =>
      ((ofMultiset d).congr (l' := φ/[t] :: Γ.toList) (by mem_tac)).exs.congr (by mem_tac)

/-- Any list that represents the end multiset carries a list derivation. -/
noncomputable def Derivation.ofMultisetEq {Δ : LK.Sequent L} (d : LK.Derivation Δ)
    (Γ : Sequent L) (h : (Γ : LK.Sequent L) = Δ) : ⊢ᶠ¹ Γ :=
  (Derivation.ofMultiset d).congr (by
    intro x hx
    rw [Multiset.mem_toList] at hx
    simpa using (h ▸ hx : x ∈ (Γ : Multiset (Proposition L))))

/-! ### 3b. Translation along a language homomorphism -/

/-- A list derivation maps along a homomorphism of languages (via the multiset calculus). -/
noncomputable def Derivation.lMap {L₁ L₂ : Language} (Φ : L₁ →ᵥ L₂) {Γ : Sequent L₁}
    (d : ⊢ᶠ¹ Γ) : ⊢ᶠ¹ Γ.map (Semiformula.lMap Φ) :=
  Derivation.ofMultisetEq (LK.Derivation.lMap Φ d.toMultiset) _ (by simp)

/-! ### 4. Consequences -/

namespace Theory.Proof

variable {T : Theory L} {φ : Sentence L}

/-- Provability is the existence of a list derivation from finitely many axioms. -/
lemma provable_iff_list :
    T ⊢ φ ↔ ∃ Γ : List (Sentence L), (∀ ψ ∈ Γ, ψ ∈ T) ∧
      Nonempty (⊢ᶠ¹ (φ : Proposition L) :: ∼Sequent.embed Γ) := by
  rw [Theory.Proof.provable_iff]
  constructor
  · rintro ⟨Γ, hΓ, ⟨d⟩⟩
    refine ⟨Γ.toList, fun ψ hψ ↦ hΓ ψ (by simpa using hψ), ⟨?_⟩⟩
    refine Derivation.ofMultisetEq d _ ?_
    rw [coe_cons, coe_tilde, coe_embed, Multiset.coe_toList, add_comm]
  · rintro ⟨Γ, hΓ, ⟨d⟩⟩
    refine ⟨(Γ : Multiset (Sentence L)), fun ψ hψ ↦ hΓ ψ (by simpa using hψ), ⟨?_⟩⟩
    refine d.toMultiset.cast ?_
    rw [coe_cons, coe_tilde, coe_embed, add_comm]

end Theory.Proof

namespace Derivation

/-- Does the list derivation have a cut-free counterpart?  Via Foundation's Hauptsatz, applied
to the multiset derivation underlying a list derivation and transported back.  The returned
list derivation is cut free because `ofMultiset` introduces no `cut` besides those it reads
off its input. -/
lemma isCutFree_ofMultiset {Δ : LK.Sequent L} {d : LK.Derivation Δ}
    (h : LK.Derivation.IsCutFree d) : Derivation.IsCutFree (Derivation.ofMultiset d) := by
  induction h with
  | identity r v => exact .contraction _ (.identity r v)
  | verum => exact .contraction _ .verum
  | or _ ih => exact .contraction _ (.or (.contraction _ ih))
  | and _ _ ih₁ ih₂ => exact .contraction _ (.and (.contraction _ ih₁) (.contraction _ ih₂))
  | all _ ih => exact .contraction _ (.all (.contraction _ ih))
  | exs t _ ih => exact .contraction _ (.exs t (.contraction _ ih))
  | contraction _ ih => exact .contraction _ ih
  | weakening _ ih => exact .contraction _ ih

namespace Canonical

/-- Cut elimination for list derivations. -/
noncomputable def hauptsatz [L.DecidableEq] {Γ : Sequent L} (d : ⊢ᶠ¹ Γ) :
    {d' : ⊢ᶠ¹ Γ // Derivation.IsCutFree d'} :=
  ⟨Derivation.ofMultisetEq (LK.Derivation.Canonical.hauptsatz d.toMultiset).1 Γ rfl,
    .contraction _ (isCutFree_ofMultiset (LK.Derivation.Canonical.hauptsatz d.toMultiset).2)⟩

end Canonical

end Derivation

end FFL.FirstOrder
