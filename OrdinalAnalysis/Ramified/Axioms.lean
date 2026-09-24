/-
  The glue: every axiom of `RAlt ν` (and of `RA Set.univ`) is derivable in the
  ramified ω-calculus, at a cut rank the level guard bounds.

  Three of `RAlt ν`'s four blocks are discharged by
  `Ramified/AxiomsLogic.lean` and `Ramified/AxiomsInduction.lean`
  (`eq_axiom_derivable`, `paMinus_axiom_derivable`, `induction_axiom_derivable`
  — none of which reads the level guard at all, since none of them cuts on a
  set atom).  The fourth, the naming schema, is `Ramified/NamingAxioms.lean`'s
  `naming_axiom_derivable`.  `RAlt_axiom_derivable` takes the naming case as a
  hypothesis `hnam`, in the same shape the other three blocks are stated in;
  the primed forms discharge it.

  `rank_evR_emb_lt_of_mem_RAlt` is the fact the level guard was introduced
  for: every axiom of `RAlt ν` (`ν ≥ 1`) has cut rank below `blkTop ν`, which is
  `ω · ν` at a finite `ν`
  (`Theory.lean`'s `lvlOf_emb_lt_of_mem_RAlt`, `Evaluate.lean`'s `lvlOf_evR`,
  and `Rank.lean`'s `rank_lt_blkTop_of_level`, composed).  This is what lets
  a proof from `RAlt ν` be replayed (`Ramified/Embed.lean`'s `replayR`) at a
  cut rank below that bound, which predicative cut elimination removes one block
  at a time (`Ramified/BlockCut.lean`).

  `RAlt_axiom_derivable'` and `RA_univ_axiom_derivable'` discharge the naming
  hypothesis with `Ramified/NamingAxioms.lean`'s `naming_axiom_derivable`.
-/
import OrdinalAnalysis.Ramified.AxiomsInduction
import OrdinalAnalysis.Ramified.Theory
import OrdinalAnalysis.Ramified.NamingAxioms

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- **The cut-rank bound the level guard buys.**  Every axiom of `RAlt ν`
(`ν ≥ 1`), evaluated and embedded, has cut rank strictly below `blkTop ν`. -/
theorem rank_evR_emb_lt_blkTop_of_mem_RAlt {ν : Lv} (hν : 1 ≤ ν) {σ : Sentence LRA}
    (h : σ ∈ RAlt ν) :
    rank (evR (Rewriting.emb σ : Proposition LRA)) < Gamma0Note.blkTop ν := by
  have hlvl : lvlOf (Rewriting.emb σ : Proposition LRA) < ν := lvlOf_emb_lt_of_mem_RAlt hν h
  have hlvl' : lvlOf (evR (Rewriting.emb σ : Proposition LRA)) < ν := by
    rw [lvlOf_evR]; exact hlvl
  exact rank_lt_blkTop_of_level hlvl'

/-- **The finite form**: every axiom of `RAlt ν` at a finite `ν ≥ 1` has cut rank
strictly below `ω · ν`. -/
theorem rank_evR_emb_lt_of_mem_RAlt {ν : ℕ} (hν : 1 ≤ ν) {σ : Sentence LRA}
    (h : σ ∈ RAlt (Gamma0Note.ofNat ν)) :
    rank (evR (Rewriting.emb σ : Proposition LRA)) < omegaMul ν := by
  rw [← blkTop_ofNat]
  exact rank_evR_emb_lt_blkTop_of_mem_RAlt
    (by rw [← Gamma0Note.ofNat_one]; exact Gamma0Note.ofNat_le_ofNat_iff.2 hν) h

/-- **Every axiom of `RAlt ν` is derivable.**  The naming case is supplied as
a hypothesis: `Ramified/NamingAxioms.lean` delivers it independently, and this
file does not depend on that file's internals. -/
theorem RAlt_axiom_derivable {ν : Lv} (hν : 1 ≤ ν)
    (hnam : ∀ σ ∈ NamingAxioms {μ | μ < ν}, ∃ β : Gamma0Note,
        OmegaDerivableR trueArithLitsR evInstR 0 β [evR (Rewriting.emb σ : Proposition LRA)]) :
    ∀ σ ∈ RAlt ν, ∃ β : Gamma0Note,
      OmegaDerivableR trueArithLitsR evInstR 0 β [evR (Rewriting.emb σ : Proposition LRA)] := by
  -- `hν` is not needed by any of the four cases below (none of them cuts on a
  -- set atom); kept in the signature to match `rank_evR_emb_lt_of_mem_RAlt`'s
  -- API.
  have _hν := hν
  rintro σ (⟨hσ, -⟩ | hσ | hσ | hσ)
  · exact eq_axiom_derivable hσ
  · exact paMinus_axiom_derivable hσ
  · exact induction_axiom_derivable hσ
  · exact hnam σ hσ

/-- **The same for `RA Set.univ`**, the ungraded theory: no level bound is
needed, since `induction_axiom_derivable` (unlike `eq_axiom_derivable` and
`paMinus_axiom_derivable`) is already uniform over every side condition on the
induction scheme. -/
theorem RA_univ_axiom_derivable
    (hnam : ∀ σ ∈ NamingAxioms Set.univ, ∃ β : Gamma0Note,
        OmegaDerivableR trueArithLitsR evInstR 0 β [evR (Rewriting.emb σ : Proposition LRA)]) :
    ∀ σ ∈ RA Set.univ, ∃ β : Gamma0Note,
      OmegaDerivableR trueArithLitsR evInstR 0 β [evR (Rewriting.emb σ : Proposition LRA)] := by
  rintro σ (hσ | hσ | hσ | hσ)
  · exact eq_axiom_derivable hσ
  · exact paMinus_axiom_derivable hσ
  · exact induction_axiom_derivable hσ
  · exact hnam σ hσ

/-- **Every axiom of `RAlt ν` is cut-free derivable**, the naming schema
included. -/
theorem RAlt_axiom_derivable' {ν : Lv} (hν : 1 ≤ ν) :
    ∀ σ ∈ RAlt ν, ∃ β : Gamma0Note,
      OmegaDerivableR trueArithLitsR evInstR 0 β [evR (Rewriting.emb σ : Proposition LRA)] :=
  RAlt_axiom_derivable hν fun _ hσ => naming_axiom_derivable hσ

/-- **Every axiom of `RA Set.univ` is cut-free derivable**, the naming schema
included. -/
theorem RA_univ_axiom_derivable' :
    ∀ σ ∈ RA Set.univ, ∃ β : Gamma0Note,
      OmegaDerivableR trueArithLitsR evInstR 0 β [evR (Rewriting.emb σ : Proposition LRA)] :=
  RA_univ_axiom_derivable fun _ hσ => naming_axiom_derivable hσ

end Ramified

end OrdinalAnalysis
