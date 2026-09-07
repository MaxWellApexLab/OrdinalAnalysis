/-
  The bridge between Foundation's concrete derivations and the ordinal-indexed
  ones.

  Both directions are needed and neither is deep.

  Forwards, every concrete derivation carries an ordinal height and a cut rank,
  so it can be replayed in the indexed calculus.  This is what lets a theorem of
  a first-order theory — obtained through Foundation's `provable_iff`, which
  turns `T ⊢ φ` into a derivation of `φ` together with negated axioms — be fed
  into cut elimination and come back with a bound.

  Backwards, an indexed derivation forgets its ordinal and its rank and becomes
  a concrete one.  That direction is what makes Foundation's semantics apply to
  everything proved here: soundness, the standard model, and the arithmetic
  hierarchy all live on `Derivation`, and none of them has to be redeveloped.

  The height assigned here is deliberately *not* Foundation's `height : ℕ`.
  Contraction is free — the indexed calculus lets a subset weaken without
  raising the bound — and branching rules take the natural sum rather than the
  maximum, which is what the reduction lemma consumes.
-/
import OrdinalAnalysis.Proof.CutElimination
import OrdinalAnalysis.Proof.CutRank
import OrdinalAnalysis.Ordinal.Notation

namespace OrdinalAnalysis

open LO LO.FirstOrder LO.FirstOrder.Derivation

variable {L : Language}

/-- The ordinal height of a concrete derivation, in any notation system.

Contraction costs nothing, because the indexed calculus absorbs it into the
subset side condition; every other rule pays a successor above the natural sum
of its premises.

The target used to be `NONote`.  It is an arbitrary `[OrdinalNotation O]`
because the replay of `Gentzen/Embed.lean` feeds the infinitary calculus, whose
heights were generalised in `Omega/Calculus.lean`, and the results above `ε₀`
need to replay into a larger notation system.  Taking `O := NONote` — which is
what `BoundedDerivable` below forces, its index still being `NONote` — gives
back exactly the old function, `OrdinalNotation.ofNat 0` being `(0 : NONote)`
and `OrdinalNotation.succ`/`nadd` the `NONote` ones by definition. -/
def ordN {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
    {Δ : Sequent L} : ⊢ᴸᴷ¹ Δ → O
  | Derivation.identity _ _ => OrdinalNotation.ofNat 0
  | Derivation.verum => OrdinalNotation.ofNat 0
  | Derivation.contraction d _ => ordN d
  | Derivation.or d => OrdinalNotation.succ (ordN d)
  | Derivation.and dp dq => OrdinalNotation.succ (OrdinalNotation.nadd (ordN dp) (ordN dq))
  | Derivation.all d => OrdinalNotation.succ (ordN d)
  | Derivation.exs d => OrdinalNotation.succ (ordN d)
  | Derivation.cut dp dn => OrdinalNotation.succ (OrdinalNotation.nadd (ordN dp) (ordN dn))

namespace BoundedDerivable

/-- **Forwards.**  Every concrete derivation is an indexed one, at its own
height and its own cut rank. -/
theorem ofDerivation {Δ : Sequent L} :
    ∀ d : ⊢ᴸᴷ¹ Δ, BoundedDerivable (cutRank d) (ordN d) Δ
  | Derivation.identity rl v => .identity rl v
  | Derivation.verum => .verum
  | Derivation.contraction d ss => by
      exact .contraction ss (ofDerivation d)
  | Derivation.or d => by
      refine .or (NONote.lt_succ _) ?_
      simpa [cutRank] using ofDerivation d
  | Derivation.and dp dq => by
      refine .and (NONote.lt_succ_of_le (NONote.le_nadd_left _ _))
        (NONote.lt_succ_of_le (NONote.le_nadd_right _ _)) ?_ ?_
      · exact (ofDerivation dp).mono_rank (by simp [cutRank])
      · exact (ofDerivation dq).mono_rank (by simp [cutRank])
  | Derivation.all d => by
      refine .all (NONote.lt_succ _) ?_
      simpa [cutRank] using ofDerivation d
  | Derivation.exs d => by
      exact .exs _ (NONote.lt_succ _) (by simpa [cutRank] using ofDerivation d)
  | Derivation.cut dp dn => by
      refine .cut ?_ (NONote.lt_succ_of_le (NONote.le_nadd_left _ _))
        (NONote.lt_succ_of_le (NONote.le_nadd_right _ _))
        ((ofDerivation dp).mono_rank (by simp [cutRank]))
        ((ofDerivation dn).mono_rank (by simp [cutRank]))
      simp only [cutRank]
      omega

/-- **Backwards.**  An indexed derivation forgets its ordinal and its rank.

This is what makes Foundation's semantics available: soundness, the standard
model, and everything built on `Derivation` transfers without redevelopment. -/
theorem toDerivation {r : ℕ} :
    ∀ {α : NONote} {Γ : Sequent L}, BoundedDerivable r α Γ → Nonempty (⊢ᴸᴷ¹ Γ) := by
  intro α Γ h
  induction h with
  | identity rl v => exact ⟨Derivation.identity rl v⟩
  | verum => exact ⟨Derivation.verum⟩
  | or _ _ ih => exact ih.map Derivation.or
  | and _ _ _ _ ihp ihq => exact ⟨Derivation.and ihp.some ihq.some⟩
  | all _ _ ih => exact ih.map Derivation.all
  | exs t _ _ ih => exact ih.map Derivation.exs
  | contraction ss _ ih => exact ih.map (fun d => Derivation.contraction d ss)
  | cut _ _ _ _ _ ihp ihn => exact ⟨Derivation.cut ihp.some ihn.some⟩

/-- The headline corollary: every concrete derivation has a cut-free indexed
counterpart, at a height bounded by an explicit tower of `ω`-powers over its
own height — and that bound is below `ε₀`, because `NONote` is the type of
notations below `ε₀`. -/
theorem cutFree_of_derivation {Δ : Sequent L} (d : ⊢ᴸᴷ¹ Δ) :
    BoundedDerivable 0 (NONote.omegaTower (cutRank d) (ordN d)) Δ :=
  cutElimination _ (ofDerivation d)

end BoundedDerivable

end OrdinalAnalysis
