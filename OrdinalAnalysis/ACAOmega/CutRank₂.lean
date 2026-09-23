/-
  The cut rank and the ordinal height of an `ACA.Derivation`.

  Direct ports of `Proof/CutRank.cutRank` and `Proof/Bridge.ordN` to
  `ACA.Derivation` (`OrdinalAnalysis/ACA/LK.lean`). The ten constructors of
  `ACA.Derivation` — `identity, cut, wk, verum, and, or, all₁, exs₁, all₂, exs₂`
  — line up one-for-one with the finitary `Derivation`'s eight: `wk` plays the
  role `contraction` did (no `Γ ⊆ Δ` side condition to record: it costs neither
  rank nor height, exactly as before), and the two new second-order rules,
  `all₂`/`exs₂`, behave for these purposes exactly like `all`/`exs` — a plain
  successor step in height, and (for `exs₂`) no interaction with the rank at
  all, because `ACA.Derivation` itself carries no cut-rank restriction: the
  bound only has to *dominate* every cut formula's rank, which `cutRank₂`
  computes by looking only at `cut`.

  * `cutRank₂ d : NONote` — `0` for a cut-free derivation, otherwise (at a
    `cut` node) `max` of `NONote.succ (rank φ)` — which is `> rank φ`, by
    `NONote.lt_succ`, exactly what the `cut` rule of `OmegaDerivable₂` demands
    — with the two premises' own ranks. This is `Proof/CutRank.cutRank` with
    `φ.complexity + 1` (a `ℕ`) replaced by `NONote.succ (ACA.rank φ)` (a
    `NONote`), since `ACA.rank` is already ordinal-valued.

  * `ordN₂ d : O`, for any `[OrdinalNotation O]` — `Proof/Bridge.ordN`'s
    pattern verbatim: `OrdinalNotation.ofNat 0` for a leaf, `OrdinalNotation.succ`
    for every one-premise rule, `OrdinalNotation.succ (OrdinalNotation.nadd _ _)`
    for the two two-premise rules (`and`, `cut`).

  Both are ordinary structural recursions on `d : ACA.Derivation Γ`, exactly as
  `cutRank`/`ordN` are on the finitary `Derivation`; Lean's equation compiler
  handles the indexing by `Γ` the same way there.
-/
import OrdinalAnalysis.ACA.LK
import OrdinalAnalysis.Ordinal.Notation

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open OrdinalAnalysis.ACA

/-- The cut rank of an `ACA.Derivation`: `0` if it uses no `cut`, and otherwise
the `max` over every `cut` node of `NONote.succ` of the cut formula's `ACA.rank`
together with the cut ranks of the two premises. -/
def cutRank₂ : {Γ : SecondOrder.Sequent ℒₒᵣ} → ACA.Derivation Γ → NONote
  | _, .identity => 0
  | _, .verum => 0
  | _, @ACA.Derivation.cut φ _ dp dn =>
      max (NONote.succ (ACA.rank φ)) (max (cutRank₂ dp) (cutRank₂ dn))
  | _, .wk d _ => cutRank₂ d
  | _, .and dp dq => max (cutRank₂ dp) (cutRank₂ dq)
  | _, .or d => cutRank₂ d
  | _, .all₁ d => cutRank₂ d
  | _, .exs₁ d => cutRank₂ d
  | _, .all₂ d => cutRank₂ d
  | _, .exs₂ _ d => cutRank₂ d

@[simp] theorem cutRank₂_identity {φ : Proposition ℒₒᵣ} :
    cutRank₂ (ACA.Derivation.identity (φ := φ)) = 0 := rfl

@[simp] theorem cutRank₂_verum : cutRank₂ ACA.Derivation.verum = 0 := rfl

@[simp] theorem cutRank₂_cut {φ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (dp : ACA.Derivation (φ :: Γ)) (dn : ACA.Derivation (∼φ :: Γ)) :
    cutRank₂ (dp.cut dn) = max (NONote.succ (ACA.rank φ)) (max (cutRank₂ dp) (cutRank₂ dn)) := rfl

@[simp] theorem cutRank₂_wk {Γ Δ : SecondOrder.Sequent ℒₒᵣ} (d : ACA.Derivation Γ) (h : Γ ⊆ Δ) :
    cutRank₂ (d.wk h) = cutRank₂ d := rfl

@[simp] theorem cutRank₂_and {φ ψ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (dp : ACA.Derivation (φ :: Γ)) (dq : ACA.Derivation (ψ :: Γ)) :
    cutRank₂ (dp.and dq) = max (cutRank₂ dp) (cutRank₂ dq) := rfl

@[simp] theorem cutRank₂_or {φ ψ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (d : ACA.Derivation (φ :: ψ :: Γ)) : cutRank₂ d.or = cutRank₂ d := rfl

@[simp] theorem cutRank₂_all₁ {φ : Semiproposition ℒₒᵣ 0 1} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (d : ACA.Derivation (φ.free₀ :: SecondOrder.Sequent.shift₀ Γ)) : cutRank₂ d.all₁ = cutRank₂ d := rfl

@[simp] theorem cutRank₂_exs₁ {φ : Semiproposition ℒₒᵣ 0 1} {t : FirstOrder.Semiterm ℒₒᵣ ℕ 0}
    {Γ : SecondOrder.Sequent ℒₒᵣ} (d : ACA.Derivation (φ/[t] :: Γ)) :
    cutRank₂ d.exs₁ = cutRank₂ d := rfl

@[simp] theorem cutRank₂_all₂ {φ : Semiproposition ℒₒᵣ 1 0} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (d : ACA.Derivation (φ.free₁ :: SecondOrder.Sequent.shift₁ Γ)) : cutRank₂ d.all₂ = cutRank₂ d := rfl

@[simp] theorem cutRank₂_exs₂ {φ : Semiproposition ℒₒᵣ 1 0} {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1}
    {Γ : SecondOrder.Sequent ℒₒᵣ} (hψ : Arith ψ) (d : ACA.Derivation (φ/⟦ψ⟧ :: Γ)) :
    cutRank₂ (d.exs₂ hψ) = cutRank₂ d := rfl

/-- Every cut formula's rank is strictly below `cutRank₂ d` — the side
condition the `cut` rule of `OmegaDerivable₂` demands, discharged once here
instead of at every replayed cut. -/
theorem rank_lt_cutRank₂_cut {φ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (dp : ACA.Derivation (φ :: Γ)) (dn : ACA.Derivation (∼φ :: Γ)) :
    ACA.rank φ < cutRank₂ (dp.cut dn) := by
  rw [cutRank₂_cut]
  exact lt_of_lt_of_le (NONote.lt_succ _) (le_max_left _ _)

/-- The ordinal height of an `ACA.Derivation`, in any notation system: a plain
successor per rule, and the natural sum of the two premises for `and`/`cut`.
Contraction being absent from `ACA.Derivation` (`wk` alone plays that role, at
no extra cost), this is `Proof/Bridge.ordN` transported rule for rule. -/
def ordN₂ {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O] :
    {Γ : SecondOrder.Sequent ℒₒᵣ} → ACA.Derivation Γ → O
  | _, .identity => OrdinalNotation.ofNat 0
  | _, .verum => OrdinalNotation.ofNat 0
  | _, .wk d _ => ordN₂ d
  | _, .and dp dq => OrdinalNotation.succ (OrdinalNotation.nadd (ordN₂ dp) (ordN₂ dq))
  | _, .or d => OrdinalNotation.succ (ordN₂ d)
  | _, .all₁ d => OrdinalNotation.succ (ordN₂ d)
  | _, .exs₁ d => OrdinalNotation.succ (ordN₂ d)
  | _, .all₂ d => OrdinalNotation.succ (ordN₂ d)
  | _, .exs₂ _ d => OrdinalNotation.succ (ordN₂ d)
  | _, .cut dp dn => OrdinalNotation.succ (OrdinalNotation.nadd (ordN₂ dp) (ordN₂ dn))

section OrdN₂Simp

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

@[simp] theorem ordN₂_identity {φ : Proposition ℒₒᵣ} :
    (ordN₂ (ACA.Derivation.identity (φ := φ)) : O) = OrdinalNotation.ofNat 0 := rfl

@[simp] theorem ordN₂_verum : (ordN₂ (ACA.Derivation.verum) : O) = OrdinalNotation.ofNat 0 := rfl

@[simp] theorem ordN₂_wk {Γ Δ : SecondOrder.Sequent ℒₒᵣ} (d : ACA.Derivation Γ) (h : Γ ⊆ Δ) :
    (ordN₂ (d.wk h) : O) = ordN₂ d := rfl

@[simp] theorem ordN₂_and {φ ψ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (dp : ACA.Derivation (φ :: Γ)) (dq : ACA.Derivation (ψ :: Γ)) :
    (ordN₂ (dp.and dq) : O) = OrdinalNotation.succ (OrdinalNotation.nadd (ordN₂ dp) (ordN₂ dq)) := rfl

@[simp] theorem ordN₂_or {φ ψ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (d : ACA.Derivation (φ :: ψ :: Γ)) : (ordN₂ d.or : O) = OrdinalNotation.succ (ordN₂ d) := rfl

@[simp] theorem ordN₂_all₁ {φ : Semiproposition ℒₒᵣ 0 1} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (d : ACA.Derivation (φ.free₀ :: SecondOrder.Sequent.shift₀ Γ)) :
    (ordN₂ d.all₁ : O) = OrdinalNotation.succ (ordN₂ d) := rfl

@[simp] theorem ordN₂_exs₁ {φ : Semiproposition ℒₒᵣ 0 1} {t : FirstOrder.Semiterm ℒₒᵣ ℕ 0}
    {Γ : SecondOrder.Sequent ℒₒᵣ} (d : ACA.Derivation (φ/[t] :: Γ)) :
    (ordN₂ d.exs₁ : O) = OrdinalNotation.succ (ordN₂ d) := rfl

@[simp] theorem ordN₂_all₂ {φ : Semiproposition ℒₒᵣ 1 0} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (d : ACA.Derivation (φ.free₁ :: SecondOrder.Sequent.shift₁ Γ)) :
    (ordN₂ d.all₂ : O) = OrdinalNotation.succ (ordN₂ d) := rfl

@[simp] theorem ordN₂_exs₂ {φ : Semiproposition ℒₒᵣ 1 0} {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1}
    {Γ : SecondOrder.Sequent ℒₒᵣ} (hψ : Arith ψ) (d : ACA.Derivation (φ/⟦ψ⟧ :: Γ)) :
    (ordN₂ (d.exs₂ hψ) : O) = OrdinalNotation.succ (ordN₂ d) := rfl

@[simp] theorem ordN₂_cut {φ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (dp : ACA.Derivation (φ :: Γ)) (dn : ACA.Derivation (∼φ :: Γ)) :
    (ordN₂ (dp.cut dn) : O) = OrdinalNotation.succ (OrdinalNotation.nadd (ordN₂ dp) (ordN₂ dn)) := rfl

end OrdN₂Simp

end OrdinalAnalysis.ACAOmega
