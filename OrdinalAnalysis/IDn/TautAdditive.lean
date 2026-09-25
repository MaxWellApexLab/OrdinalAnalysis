/-
  Reprove `IDn/Embed.lean`'s `EmbedHyps.taut` field under `IDn/Rank.lean`'s *additive*
  height convention (height `rk ψ`, no `omegaMul`), as opposed to `IDn/AxiomsLogic.lean`'s
  `taut` (Freund Lemma 6.1), which delivers height `omegaMul (rk ψ)`.

  **Finding: the field, exactly as stated, is FALSE**, not merely hard to prove at the stated
  height. `EmbedHyps.taut` (`Embed.lean` lines ~103-107) reads

    `taut : ∀ {H}, NiceS H → ∀ ψ, ψ.freeVariables = ∅ →
      IDnDerivable A zero (adjoin H (Stage.val '' params ψ)) (rk ψ) [ψ, ∼ψ]`

  and this is refuted below (`taut_additive_impossible`) at `ψ := ∀¹ (X(#0))`, `X` the free
  predicate (`IDn/Language.lean`'s `XinfAt`) applied to the bound variable — i.e. `ψ = ∀x.X(x)`,
  the simplest possible closed formula with a leading quantifier and no other structure.

  **Why.** The *only* calculus clause that can introduce `∀¹φ` as a proven disjunct (`IDn/
  Calculus.lean`'s `IDnDerivable.all`, the ω-rule) requires, to derive `H ⊢^α [∀¹φ, Γ]`, a
  family `f : ℕ → ThetaWNoteD` with `∀ m, f m < α` *and* `∀ m, H ⊢^{f m} [φ/[numI m], Γ]` — i.e.
  `α` must exceed `f m` for *every* natural `m` simultaneously. When `Γ = [∼(∀¹φ)] = [∃¹(∼φ)]`
  and `φ = X(#0)`, each branch `[X(m̄), ∃¹(∼φ)]` can *only* close via `.idX` (`X(m̄)` and some
  witness `∼X(p̄)` for the *same* numeral, forced by term injectivity — every other clause is
  excluded by a formula-shape mismatch, checked exhaustively below), and `.exs`'s own witness
  side-condition (`ofNat p < height`) forces `f m ≥ ofNat m` (`key_aux` below, by induction on
  the derivation, tracking the accumulated negative witnesses as a list disjoint from the target
  index). Hence `α` must dominate `{ofNat m : m ∈ ℕ}`, i.e. `α ≥ ω` (`ThetaWNoteD.omegaPow one`,
  `taut_additive_impossible`'s closing step). But `rk (∀¹ (X(#0))) = ThetaWNoteD.succ
  (atomRk X) = ThetaWNoteD.succ ThetaWNoteD.zero = ThetaWNoteD.one`, and `one < omegaPow one`
  (`ofNat_lt_omega`-style fact) — a *finite successor*, nowhere near `ω`. So no `α` at all can
  equal `rk (∀¹φ)` and satisfy the `all`-rule's requirement: **the field is unsatisfiable for
  any closed formula whose outermost shape is `∀¹`/`∃¹`**, regardless of `A`, `H`, or the rest of
  `EmbedHyps`.

  This is not an artifact of one proof strategy: `IDnDerivable`'s only two constructors whose
  principal formula can be `∀¹φ` or `∃¹(∼φ)` are `.all`/`.exs` themselves (checked by exhaustive
  shape-mismatch on the other nine — `.literal`/`.verum` fail since neither formula is `TrueLit`/
  `⊤`; `.idX`/`.stage`/`.nstage`/`.fix` fail since neither is `X`/stage-shaped; `.and`/`.orL`/
  `.orR` fail since neither is `∧`/`∨`-shaped; `.cut` fails unconditionally since it needs
  `rk ψ < ρ = ThetaWNoteD.zero`, impossible). So the argument is exhaustive, not just the
  natural one.

  **The correct bound.** `IDn/AxiomsLogic.lean`'s `taut` already proves exactly the needed
  height, `omegaMul (rk ψ)` (`ω · rk ψ`), which *does* dominate `ω` regardless of `rk ψ`'s size
  (`ThetaWNoteD.le_omegaMul`/`omegaMul_zero`-adjacent facts) and is the height Freund's Lemma 6.1
  uses for exactly this reason. **Conclusion: `EmbedHyps.taut`'s field must be changed from
  height `rk ψ` to height `omegaMul (rk ψ)`** — at which point it is *already proven* by
  `IDn.taut` (modulo the `FamilyLevelBounded A` hypothesis that theorem needs and the field does
  not thread through, the same gap already flagged for `eq_axiom`). No new "reprove Lemma 6.1 additively" work is mathematically
  available to do beyond this: the fallback ("if a case genuinely needs a height
  above `rk ψ`, ... the `EmbedHyps` field itself must change") is the outcome here, for the
  `all`/`exs` case specifically (the `and`/`or` cases have a milder, `+1`-scale gap that *would*
  be closeable by a tighter bound; the `all`/`exs` gap is the one no finite rescaling of `rk ψ`
  can ever close, so it is the binding obstruction and the only one formalised here).

  No `sorry`, no new axiom, no `native_decide`, no `partial def`; `autoImplicit false`.
-/
import OrdinalAnalysis.IDn.AxiomsLogic

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder

variable {n : ℕ}

/-! ### The witness formula `X(#0)` and its numeral instances -/

section TautAdditiveImpossible

variable {A : Fin n → Semisentence (LXIn n) 1}

/-- The free-predicate atom `X(#0)`: the simplest possible closed formula once `∀¹`-wrapped. -/
def tautWitness (n : ℕ) : Semiproposition (LIinfN n) 1 := XinfAt (#0 : Semiterm (LIinfN n) ℕ 1)

/-- `¬X(m̄)`, the numeral instance at `m` of the negation of `tautWitness`. -/
def negXAt (n : ℕ) (m : ℕ) : Proposition (LIinfN n) := ∼ (XinfAt (numI m))

@[simp] theorem tautWitness_subst (m : ℕ) :
    (tautWitness n)/[numI m] = XinfAt (numI m) := by
  have e : (tautWitness n)/[numI m]
      = (Rew.subst ![numI m] : Rew (LIinfN n) ℕ 1 ℕ 0) ▹ (tautWitness n) := rfl
  have e2 := Semiformula.rew_rel (Rew.subst ![numI m] : Rew (LIinfN n) ℕ 1 ℕ 0)
    (Sum.inr IInfRelN.X : (LIinfN n).Rel 1) ![(#0 : Semiterm (LIinfN n) ℕ 1)]
  rw [e, show tautWitness n
    = Semiformula.rel (Sum.inr IInfRelN.X : (LIinfN n).Rel 1) ![(#0 : Semiterm (LIinfN n) ℕ 1)]
    from rfl, e2, XinfAt]
  congr 1
  funext i
  fin_cases i
  rfl

@[simp] theorem rk_tautWitness : rk (tautWitness n) = ThetaWNoteD.zero := rk_XinfAt _

@[simp] theorem rk_all_tautWitness : rk (∀¹ (tautWitness n)) = ThetaWNoteD.one := by
  rw [rk_all, rk_tautWitness]
  exact ThetaWNoteD.zero_nadd _

/-! ### Formula-shape exclusions

A coarse, decidable "top shape" tag, used to discriminate formulas by their outermost
constructor (and, for atoms, by the `IInfRelN` tag) without ever destructuring a `rel`/`nrel`
equality via `injection` (which drags in an unwanted arity-`HEq` since the arithmetic relation's
arity `j` is existentially bound). Reading off `fShape` from an equality of formulas via
`congrArg` and then discriminating on the (decidable-equality) `FShape` value is robust and
reusable across every shape-mismatch case below. -/

inductive FShape where
  | verum | falsum | arithRel | arithNrel | xRel | xNrel | stageRel | stageNrel
  | and | or | all | exs
  deriving DecidableEq

/-- The outermost shape of a proposition. -/
def fShape : Proposition (LIinfN n) → FShape
  | .verum => .verum
  | .falsum => .falsum
  | .rel (Sum.inl _) _ => .arithRel
  | .rel (Sum.inr IInfRelN.X) _ => .xRel
  | .rel (Sum.inr (IInfRelN.stage _)) _ => .stageRel
  | .nrel (Sum.inl _) _ => .arithNrel
  | .nrel (Sum.inr IInfRelN.X) _ => .xNrel
  | .nrel (Sum.inr (IInfRelN.stage _)) _ => .stageNrel
  | .and _ _ => .and
  | .or _ _ => .or
  | .all _ => .all
  | .exs _ => .exs

@[simp] theorem fShape_verum : fShape (⊤ : Proposition (LIinfN n)) = .verum := rfl

@[simp] theorem fShape_falsum : fShape (⊥ : Proposition (LIinfN n)) = .falsum := rfl

@[simp] theorem fShape_XinfAt (t : SyntacticTerm (LIinfN n)) : fShape (XinfAt t) = .xRel := by
  simp [XinfAt, fShape]

theorem negXinfAt_eq_nrel (t : SyntacticTerm (LIinfN n)) :
    (∼ (XinfAt t) : Proposition (LIinfN n)) = Semiformula.nrel (Sum.inr IInfRelN.X) ![t] := by
  rw [XinfAt]; rfl

@[simp] theorem fShape_negXinfAt (t : SyntacticTerm (LIinfN n)) :
    fShape (∼ (XinfAt t) : Proposition (LIinfN n)) = .xNrel := by
  rw [negXinfAt_eq_nrel]; rfl

@[simp] theorem fShape_stageAt (s : Stage n) (t : SyntacticTerm (LIinfN n)) :
    fShape (stageAt s t) = .stageRel := by
  simp [stageAt, fShape]

@[simp] theorem fShape_nstageAt (s : Stage n) (t : SyntacticTerm (LIinfN n)) :
    fShape (nstageAt s t) = .stageNrel := by
  simp [nstageAt, fShape]

@[simp] theorem fShape_IOmegaAt (k : Fin n) (t : SyntacticTerm (LIinfN n)) :
    fShape (IOmegaAt k t) = .stageRel := by
  simp [IOmegaAt, stageAt, fShape]

@[simp] theorem fShape_exs {φ : Semiproposition (LIinfN n) 1} : fShape (∃¹ φ) = .exs := rfl

@[simp] theorem fShape_all {φ : Semiproposition (LIinfN n) 1} : fShape (∀¹ φ) = .all := rfl

@[simp] theorem fShape_and {φ ψ : Proposition (LIinfN n)} : fShape (φ ⋏ ψ) = .and := rfl

@[simp] theorem fShape_or {φ ψ : Proposition (LIinfN n)} : fShape (φ ⋎ ψ) = .or := rfl

theorem fShape_of_isArithLit {φ : Proposition (LIinfN n)} (h : IsArithLit φ) :
    fShape φ = .arithRel ∨ fShape φ = .arithNrel := by
  obtain ⟨j, r, v, rfl | rfl, -⟩ := h
  · exact Or.inl (by simp [fShape])
  · exact Or.inr (by simp [fShape])

theorem not_isArithLit_XinfAt (t : SyntacticTerm (LIinfN n)) : ¬ IsArithLit (XinfAt t) := by
  intro h
  rcases fShape_of_isArithLit h with h' | h' <;> simp at h'

theorem not_isArithLit_negXinfAt (t : SyntacticTerm (LIinfN n)) : ¬ IsArithLit (∼ (XinfAt t)) := by
  intro h
  rcases fShape_of_isArithLit h with h' | h' <;> simp at h'

theorem not_isArithLit_exs {φ : Semiproposition (LIinfN n) 1} : ¬ IsArithLit (∃¹ φ) := by
  intro h
  rcases fShape_of_isArithLit h with h' | h' <;> simp at h'

/-- Numerals are injective, via their value in the standard model. -/
theorem numI_inj {p q : ℕ} (h : (numI p : SyntacticTerm (LIinfN n)) = numI q) : p = q := by
  have heval := congrArg (Semiterm.val (s := stdInfN) (![] : Fin 0 → ℕ) (fun _ : ℕ => 0)) h
  rwa [val_numI, val_numI] at heval

/-- The `X`-argument of an `X`-shaped or `¬X`-shaped proposition, junk (`&0`) otherwise. -/
def xArg : Proposition (LIinfN n) → SyntacticTerm (LIinfN n)
  | .rel (Sum.inr IInfRelN.X) v => v 0
  | .nrel (Sum.inr IInfRelN.X) v => v 0
  | _ => Semiterm.fvar 0

@[simp] theorem xArg_XinfAt (t : SyntacticTerm (LIinfN n)) : xArg (XinfAt t) = t := by
  simp [XinfAt, xArg]

@[simp] theorem xArg_negXinfAt (t : SyntacticTerm (LIinfN n)) :
    xArg (∼ (XinfAt t) : Proposition (LIinfN n)) = t := by
  rw [negXinfAt_eq_nrel]; rfl

/-- `X(p̄) = X(q̄)` forces `p = q`. -/
theorem xinfAt_numI_inj {p q : ℕ}
    (h : (XinfAt (numI p) : Proposition (LIinfN n)) = XinfAt (numI q)) : p = q := by
  have := congrArg xArg h
  rw [xArg_XinfAt, xArg_XinfAt] at this
  exact numI_inj this

/-- `¬X(p̄) = ¬X(q̄)` forces `p = q`. -/
theorem negXinfAt_numI_inj {p q : ℕ}
    (h : (∼ (XinfAt (numI p)) : Proposition (LIinfN n)) = ∼ (XinfAt (numI q))) : p = q := by
  have := congrArg xArg h
  rw [xArg_negXinfAt, xArg_negXinfAt] at this
  exact numI_inj this

/-! ### `key_aux`: the omega-rule's witness must dominate every natural number -/

/-- Membership in the target sequent, decomposed. -/
theorem mem_shape {q : ℕ} {L : List ℕ} {φ : Proposition (LIinfN n)}
    (h : φ ∈ (L.map (negXAt n)) ++ [XinfAt (numI q), ∃¹ (∼ (tautWitness n))]) :
    (∃ k ∈ L, φ = negXAt n k) ∨ φ = XinfAt (numI q) ∨ φ = ∃¹ (∼ (tautWitness n)) := by
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with ⟨k, hk, hke⟩ | h | h
  · exact Or.inl ⟨k, hk, hke.symm⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **The key induction.** If `X(q̄)`, together with some negative `X`-literals at indices `L`
(`q ∉ L`) and the fixed tail `∃¹(¬tautWitness)`, is derivable at height `α`, then `α` already
exceeds `ofNat q`. Only `.exs` can ever produce such a derivation (every other clause is excluded
by a formula-shape mismatch, `.cut` unconditionally since `rk _ < zero` is impossible), and its
own witness side-condition (`ofNat p < height`) is what forces the bound — either directly, when
the witness happens to be `q` itself, or after one more layer of `.exs` recursion otherwise. -/
theorem key_aux {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    (d : IDnDerivable A ThetaWNoteD.zero H α Γ) :
    ∀ (q : ℕ) (L : List ℕ), q ∉ L →
      Γ = (L.map (negXAt n)) ++ [XinfAt (numI q), ∃¹ (∼ (tautWitness n))] →
      ThetaWNoteD.ofNat q < α := by
  induction d with
  | literal hα hΓ hφ hm =>
    intro q L hqL hEq
    subst hEq
    exfalso
    rcases mem_shape hm with ⟨k, hk, rfl⟩ | rfl | rfl
    · exact not_isArithLit_negXinfAt _ hφ.1
    · exact not_isArithLit_XinfAt _ hφ.1
    · exact not_isArithLit_exs hφ.1
  | verum hα hΓ hm =>
    intro q L hqL hEq
    subst hEq
    exfalso
    rcases mem_shape hm with ⟨k, hk, heq⟩ | heq | heq <;>
      exact absurd (congrArg fShape heq) (by simp [negXAt])
  | idX t hα hΓ h1 h2 =>
    intro q L hqL hEq
    subst hEq
    exfalso
    rcases mem_shape h1 with ⟨k, hk, heq1⟩ | heq1 | heq1
    · exact absurd (congrArg fShape heq1) (by simp [negXAt])
    · have ht : t = numI q := by simpa using congrArg xArg heq1
      subst ht
      rcases mem_shape h2 with ⟨k, hk, heq2⟩ | heq2 | heq2
      · have hqk : q = k := negXinfAt_numI_inj (by rw [negXAt] at heq2; exact heq2)
        exact hqL (hqk ▸ hk)
      · exact absurd (congrArg fShape heq2) (by simp)
      · exact absurd (congrArg fShape heq2) (by simp)
    · exact absurd (congrArg fShape heq1) (by simp)
  | and hα hΓ hm h0 h1 d0 d1 ih0 ih1 =>
    intro q L hqL hEq
    subst hEq
    exfalso
    rcases mem_shape hm with ⟨k, hk, heq⟩ | heq | heq <;>
      exact absurd (congrArg fShape heq) (by simp [negXAt])
  | orL hα hΓ hm h0 d0 ih0 =>
    intro q L hqL hEq
    subst hEq
    exfalso
    rcases mem_shape hm with ⟨k, hk, heq⟩ | heq | heq <;>
      exact absurd (congrArg fShape heq) (by simp [negXAt])
  | orR hα hΓ hm h1 h0 d0 ih0 =>
    intro q L hqL hEq
    subst hEq
    exfalso
    rcases mem_shape hm with ⟨k, hk, heq⟩ | heq | heq <;>
      exact absurd (congrArg fShape heq) (by simp [negXAt])
  | all f hα hΓ hm hf d0 ih0 =>
    intro q L hqL hEq
    subst hEq
    exfalso
    rcases mem_shape hm with ⟨k, hk, heq⟩ | heq | heq <;>
      exact absurd (congrArg fShape heq) (by simp [negXAt])
  | exs m hα hΓ hm hn h0 d0 ih0 =>
    intro q L hqL hEq
    subst hEq
    rcases mem_shape hm with ⟨k, hk, heq⟩ | heq | heq
    · exact absurd (congrArg fShape heq) (by simp [negXAt])
    · exact absurd (congrArg fShape heq) (by simp)
    · injection heq with _ hφ
      subst hφ
      by_cases hmq : m = q
      · subst hmq
        exact hn
      · have hqL' : q ∉ (m :: L) := fun h => (List.mem_cons.mp h).elim (Ne.symm hmq) hqL
        exact lt_trans (ih0 q (m :: L) hqL' (by simp [negXAt])) h0
  | stage g hα hΓ hm hga hgα hgH h0 d0 ih0 =>
    intro q L hqL hEq
    subst hEq
    exfalso
    rcases mem_shape hm with ⟨k, hk, heq⟩ | heq | heq <;>
      exact absurd (congrArg fShape heq) (by simp [negXAt])
  | nstage f hα hΓ hm hf d0 ih0 =>
    intro q L hqL hEq
    subst hEq
    exfalso
    rcases mem_shape hm with ⟨k, hk, heq⟩ | heq | heq <;>
      exact absurd (congrArg fShape heq) (by simp [negXAt])
  | fix hα hΓ hm hΩ h0 d0 ih0 =>
    intro q L hqL hEq
    subst hEq
    exfalso
    rcases mem_shape hm with ⟨k, hk, heq⟩ | heq | heq <;>
      exact absurd (congrArg fShape heq) (by simp [negXAt])
  | cut hα hΓ hr h0 d0 d1 ih0 ih1 =>
    intro q L hqL hEq
    exact absurd hr not_lt_bot

/-! ### The impossibility theorem -/

/-- **`EmbedHyps.taut` is false at height `rk psi`**, for `psi := forall x. X(x)` (`X` the free
predicate, applied to the bound variable): no `IDnDerivable` derivation of `[psi, not psi]` at
height `rk psi` exists, for *any* operator `H` (in particular for any `NiceS H`) and *any* `A`.
`.all` is the only clause that can introduce `forall (tautWitness n)`; `inv_all` (already proved,
`Calculus.lean`, needs only `IsOperator H`) strips it *at the same height*, handing `key_aux`
exactly its base case (`L := []`) for every instance `q`. `key_aux` then forces
`ofNat q < rk (forall (tautWitness n))` for every `q : Nat`, but `rk (forall (tautWitness n)) =
one` (`rk_all_tautWitness`) and `ofNat 1 = one`, so `q := 1` gives `one < one` — absurd. -/
theorem taut_additive_impossible {H : Set ThetaWNoteD → Set ThetaWNoteD}
    (hH : ThetaWNoteD.IsOperator H) :
    ¬ IDnDerivable A ThetaWNoteD.zero H (rk (∀¹ (tautWitness n)))
        [∀¹ (tautWitness n), ∼ (∀¹ (tautWitness n))] := by
  intro d
  have hall : ∀ q : ℕ, IDnDerivable A ThetaWNoteD.zero H (rk (∀¹ (tautWitness n)))
      (XinfAt (numI q) :: [∃¹ (∼ (tautWitness n))]) := by
    intro q
    have hd : IDnDerivable A ThetaWNoteD.zero H (rk (∀¹ (tautWitness n)))
        ((∀¹ (tautWitness n)) :: [∃¹ (∼ (tautWitness n))]) := d
    have := IDnDerivable.inv_all hH q hd
    simpa using this
  have hkey : ∀ q : ℕ, ThetaWNoteD.ofNat q < rk (∀¹ (tautWitness n)) := fun q =>
    key_aux (hall q) q [] (by simp) (by simp)
  have h1 := hkey 1
  rw [rk_all_tautWitness, ← ThetaWNoteD.ofNat_one] at h1
  exact absurd h1 (lt_irrefl _)

end TautAdditiveImpossible

end IDn

end OrdinalAnalysis
