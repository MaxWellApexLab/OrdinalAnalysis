/-
  Transport of derivations along a map of formulas.

  The infinitary calculus is parametrised by how quantifiers are instantiated.
  Two instantiations are in play: plain substitution, under which the
  ω-completeness of true X-free sentences is proved, and substitution followed
  by evaluation of closed terms, under which PA[X] proofs are replayed.  This
  file moves derivations from the first to the second, and more generally along
  any map of formulas that respects the rules: commutes with the connectives
  and with negation, preserves complexity, carries axioms to axioms, keeps
  relation symbols, and intertwines the two instantiations.

  The proof is a plain induction on the derivation; every rule is closed under
  the map by one of the listed properties, and nothing about ordinals or ranks
  changes.
-/
import OrdinalAnalysis.Omega.Calculus

namespace OrdinalAnalysis

open LO LO.FirstOrder

variable {L : Language}

namespace OmegaDerivable

/-- A map of formulas along which derivations can be transported from the
instantiation `I` to the instantiation `J`. -/
structure Transport (A : Literals L) (I J : Instantiation L) where
  /-- The map, at every binder depth. -/
  F : ∀ {n : ℕ}, Semiformula L ℕ n → Semiformula L ℕ n
  F_verum : ∀ {n : ℕ}, F (⊤ : Semiformula L ℕ n) = ⊤
  F_or : ∀ {n : ℕ} (φ ψ : Semiformula L ℕ n), F (φ ⋎ ψ) = F φ ⋎ F ψ
  F_and : ∀ {n : ℕ} (φ ψ : Semiformula L ℕ n), F (φ ⋏ ψ) = F φ ⋏ F ψ
  F_all : ∀ {n : ℕ} (φ : Semiformula L ℕ (n + 1)), F (∀¹ φ) = ∀¹ (F φ)
  F_exs : ∀ {n : ℕ} (φ : Semiformula L ℕ (n + 1)), F (∃¹ φ) = ∃¹ (F φ)
  F_neg : ∀ {n : ℕ} (φ : Semiformula L ℕ n), F (∼φ) = ∼(F φ)
  F_complexity : ∀ {n : ℕ} (φ : Semiformula L ℕ n), (F φ).complexity = φ.complexity
  /-- The map intertwines the two instantiations. -/
  F_inst : ∀ (φ : Semiproposition L 1) (n : ℕ), F (I.inst φ n) = J.inst (F φ) n
  /-- Axioms go to axioms. -/
  F_atom : ∀ φ : Proposition L, A.T φ → A.T (F φ)
  /-- An atom keeps its relation symbol. -/
  F_rel : ∀ {k : ℕ} (rl : L.Rel k) (v : Fin k → SyntacticTerm L),
    ∃ v' : Fin k → SyntacticTerm L, F (Semiformula.rel rl v) = Semiformula.rel rl v'

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals L} {I J : Instantiation L}

/-- **Transport.**  A derivation under `I` becomes a derivation of the mapped
sequent under `J`, at the same rank and height. -/
theorem transport (T : Transport A I J) {r : ℕ} :
    ∀ {α : O} {Γ : Sequent L}, OmegaDerivable A I r α Γ →
      OmegaDerivable A J r α (Γ.map T.F) := by
  intro α Γ h
  induction h with
  | atom hφ =>
      simp only [List.map_cons, List.map_nil]
      exact .atom (T.F_atom _ hφ)
  | identity rl v =>
      obtain ⟨v', hv⟩ := T.F_rel rl v
      have hn : T.F (Semiformula.nrel rl v) = Semiformula.nrel rl v' := by
        rw [← Semiformula.neg_rel, T.F_neg, hv, Semiformula.neg_rel]
      simp only [List.map_cons, List.map_nil, hv, hn]
      exact .identity rl v'
  | verum =>
      simp only [List.map_cons, List.map_nil, T.F_verum]
      exact .verum
  | or hlt _ ih =>
      simp only [List.map_cons] at ih ⊢
      rw [T.F_or]
      exact .or hlt ih
  | and hb hc _ _ ihp ihq =>
      simp only [List.map_cons] at ihp ihq ⊢
      rw [T.F_and]
      exact .and hb hc ihp ihq
  | omegaRule f hf _ ih =>
      simp only [List.map_cons] at ih ⊢
      rw [T.F_all]
      refine .omegaRule f hf (fun n => ?_)
      have := ih n
      rw [T.F_inst] at this
      exact this
  | exs n hlt _ ih =>
      simp only [List.map_cons] at ih ⊢
      rw [T.F_exs]
      refine .exs n hlt ?_
      rw [T.F_inst] at ih
      exact ih
  | contraction ss _ ih =>
      exact .contraction (List.map_subset _ ss) ih
  | cut hc hb hg _ _ ihp ihn =>
      simp only [List.map_cons] at ihp ihn
      rw [T.F_neg] at ihn
      rw [List.map_append]
      exact .cut (by rw [T.F_complexity]; exact hc) hb hg ihp ihn

end OmegaDerivable

end OrdinalAnalysis
