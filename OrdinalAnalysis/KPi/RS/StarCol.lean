module

public import OrdinalAnalysis.KPi.RS.StarAxFinal

/-!
# The RS calculus, part 22: Theorem 2.9 (b), the `(Ref)*`-leaf for `(Δ₀-Col)`

B92 Thm 2.9 (b): `⊢*_1 (Δ₀-Col)^κ` for `κ ∈ R`, "an immediate consequence of (Ref)*".  The instance of
`(Δ₀-Col)^κ` at parameters `c⃗, w` is `A → ∃w₁∈L_κ ∀x∈w ∃y∈w₁ φ(x,y,c⃗)` with
`A ≡ ∀x∈w ∃y∈L_κ φ(x,y,c⃗)`, a `Σ(κ)`-sentence: `A ≡ ψ^{L_κ}(c⃗, w)` where
`ψ(c⃗, w, d) = ∀x∈w ∃y∈d φ`.  `colSigma` is this `SigmaData` (domain variable `d` = last), and
`star_col_leaf` is the corresponding `(Ref)*` axiom.

NOTE (presentation).  `Star.ref` takes any sentence `X` that is `Sim`-equivalent to the
`RSS`-level disjunction `RSS.or S.sentence.neg S.refl` (with `d` the *last* environment entry), so the
`D0`-level sentence `base (or ¬A C) ρ` (the matrix of the closed `(Δ₀-Col)^b`) is an instance of the
axiom; this is used in `StarColAx` (`star_col`).
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}} {σ : Ordinal.{1}}

/-- no level constant occurs as a bound. -/
def D0.NoLev : {n : ℕ} → D0 n → Prop
  | _, .mem _ _ => True
  | _, .nmem _ _ => True
  | _, .ad _ => True
  | _, .nad _ => True
  | _, .and A B => D0.NoLev A ∧ D0.NoLev B
  | _, .or A B => D0.NoLev A ∧ D0.NoLev B
  | _, .bex (.var _) A => D0.NoLev A
  | _, .bex (.lev _) _ => False
  | _, .ball (.var _) A => D0.NoLev A
  | _, .ball (.lev _) _ => False

theorem isSigma_rename : ∀ {m k : ℕ} (A : D0 m) (f : Fin m → Fin k) (d : Fin k),
    D0.NoLev A → (∀ i, f i ≠ d) → IsSigma d (A.rename f)
  | _, _, .mem i j, f, d, _, hf => ⟨hf i, hf j⟩
  | _, _, .nmem i j, f, d, _, hf => ⟨hf i, hf j⟩
  | _, _, .ad i, f, d, _, hf => hf i
  | _, _, .nad i, f, d, _, hf => hf i
  | _, _, .and A B, f, d, h, hf => ⟨isSigma_rename A f d h.1 hf, isSigma_rename B f d h.2 hf⟩
  | _, _, .or A B, f, d, h, hf => ⟨isSigma_rename A f d h.1 hf, isSigma_rename B f d h.2 hf⟩
  | _, _, .bex (.var j) A, f, d, h, hf => by
    refine isSigma_rename A (liftF f) d.castSucc h ?_
    intro i
    induction i using Fin.lastCases with
    | last => simpa using (Fin.castSucc_lt_last d).ne'
    | cast j => simpa using hf j
  | _, _, .ball (.var j) A, f, d, h, hf => by
    refine ⟨hf j, isSigma_rename A (liftF f) d.castSucc h ?_⟩
    intro i
    induction i using Fin.lastCases with
    | last => simpa using (Fin.castSucc_lt_last d).ne'
    | cast j => simpa using hf j

/-- `φ(x, y, c⃗)` (`D0 (k+2)`, context `[c⃗, x, y]`) placed in `[c⃗, w, d, x, y]`. -/
def colPlace {k : ℕ} (φ : D0 (k + 2)) : D0 (k + 4) :=
  φ.rename (ext (ext (fun j : Fin k => j.castSucc.castSucc.castSucc.castSucc)
    (Fin.castSucc (Fin.last (k + 2)))) (Fin.last (k + 3)))

/-- `ψ(c⃗, w, d) = ∀x∈w ∃y∈d φ(x, y, c⃗)`, with `d` the last variable. -/
def colPsi {k : ℕ} (φ : D0 (k + 2)) : D0 (k + 2) :=
  D0.ball (Bd.var (Fin.castSucc (Fin.last k)))
    (D0.bex (Bd.var (Fin.castSucc (Fin.last (k + 1)))) (colPlace φ))

theorem isSigma_colPsi {k : ℕ} (φ : D0 (k + 2)) (hφ : D0.NoLev φ) :
    IsSigma (Fin.last (k + 1)) (colPsi φ) := by
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg Fin.val h
    simp at this
  · refine isSigma_rename φ _ _ hφ ?_
    intro i
    induction i using Fin.lastCases with
    | last =>
      intro h
      have := congrArg Fin.val h
      simp at this
    | cast i =>
      induction i using Fin.lastCases with
      | last =>
        intro h
        have := congrArg Fin.val h
        simp at this
      | cast j =>
        intro h
        have := congrArg Fin.val h
        have hj := j.2
        simp at this
        omega

/-- the `Σ(κ)`-datum of the antecedent `A ≡ ∀x∈w ∃y∈L_κ φ(x,y,c⃗)` of `(Δ₀-Col)^κ`. -/
def colSigma {κ : Ordinal.{1}} {k : ℕ} (φ : D0 (k + 2)) (hφ : D0.NoLev φ) (c : Fin k → T)
    (w : T) (hc : ∀ i, (c i).level < κ) (hw : w.level < κ) : SigmaData κ where
  m := k + 1
  φ := colPsi φ
  hφ := isSigma_colPsi φ hφ
  ρ := ext c w
  hρ := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa using hw
    | cast j => simpa using hc j

/-- **B92 Thm 2.9 (b)** (the `(Ref)*` axiom for the instance of `(Δ₀-Col)^κ`):
`⊢*_σ A → ∃w₁∈L_κ ∀x∈w ∃y∈w₁ φ(x,y,c⃗)`, `σ > 0`, `κ ∈ R`. -/
theorem star_col_leaf {κ : Ordinal.{1}} (hκ : κ ∈ R) {k : ℕ} (φ : D0 (k + 2)) (hφ : D0.NoLev φ)
    (c : Fin k → T) (w : T) (hc : ∀ i, (c i).level < κ) (hw : w.level < κ) (hσ : 0 < σ)
    {Γ : Set RSS} :
    Star R σ (insert (RSS.or (colSigma φ hφ c w hc hw).sentence.neg
      (colSigma φ hφ c w hc hw).refl) Γ) :=
  Star.ref (colSigma φ hφ c w hc hw) hκ hσ (Sim.refl _)

end OrdinalAnalysis.KPi.RS
