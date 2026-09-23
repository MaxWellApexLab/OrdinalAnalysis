/-
  The parametric lifting `toSOAtB ψ`, the
  first-order-to-second-order derivation translator `translate ψ`, and the
  commutation lemmas the capstone `lift_paLX` (`Lift.lean`) needs.

  The route (design note §0.2): the only place `paLX` (`Gentzen/Setup.lean`)
  mentions the fresh predicate `X` is through `Xat t`; `toSOAtB ψ` replaces
  every such atom by `ψ/[unTerm t]` for an arbitrary second-order `ψ` (set
  quantifiers in `ψ` are fine — it is a formula of the *ambient* ACA syntax,
  not a witness for `exs₂`).  Because the only `paLX` axiom mentioning `X` is
  `𝗘𝗤 LX`'s `relExt (Sum.inr XRel.X)`, and every other axiom is `X`-free, the
  translated derivation of any `paLX`-theorem is closeable in `ACA` using
  `setExt`'s image (`congruence`) in that one spot and ordinary lifted `PA⁻`/
  induction elsewhere.

  **Why the bound-set-slot count `N`.**  `ACA`'s induction scheme is an axiom
  only for formulas with *no free set variable* (`LK.lean`, defect (D2)); but
  the parameters the design needs (`#0 ∈& 0`, `Jump(X₀)`) are free set
  variables, so the image of `paLX`'s induction axiom under `toSOAt` at such a
  `ψ` is not an axiom.  The fix is to keep `ψ`'s set parameters in *bound
  slots*: `toSOAtB ψ` for `ψ : Semiformula ℒₒᵣ ℕ Empty N 1` lands in
  `Semiformula ℒₒᵣ ℕ ℕ N n`, whose image of the induction axiom is the closed
  `indScheme₂`, and the free-variable instance is recovered afterwards by
  `Toolkit.lean`'s `specSets` — which is exactly `subst₁_toSOAtB` below.
  `toSOAt := toSOAtB (N := 0)` keeps every earlier use unchanged.
-/
import OrdinalAnalysis.ACA.Toolkit

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX XRel Xat toLX paLX)

/-! ### Erasing the fresh predicate from a term

`LX`'s function symbols are exactly `ℒₒᵣ`'s (`XLang` contributes none), so
every `LX`-term is the image of an `ℒₒᵣ`-term under `toLX`; `unTerm` is the
inverse read off directly from the term's shape. -/

/-- **Erase `X` from a term.**  Well-defined because `XLang` has no function
symbols: the `Sum.inr` case of `LX.Func` is `PEmpty`. -/
def unTerm {ξ : Type*} {n : ℕ} : FirstOrder.Semiterm LX ξ n → FirstOrder.Semiterm ℒₒᵣ ξ n
  | .bvar x => .bvar x
  | .fvar x => .fvar x
  | .func (Sum.inl f) v => .func f (fun i => unTerm (v i))
  | .func (Sum.inr e) _ => e.elim

@[simp] theorem unTerm_bvar {ξ : Type*} {n : ℕ} (x : Fin n) :
    (unTerm (#x : FirstOrder.Semiterm LX ξ n)) = #x := rfl

@[simp] theorem unTerm_fvar {ξ : Type*} {n : ℕ} (x : ξ) :
    (unTerm (&x : FirstOrder.Semiterm LX ξ n)) = &x := rfl

@[simp] theorem unTerm_func {ξ : Type*} {n k : ℕ} (f : (ℒₒᵣ).Func k)
    (v : Fin k → FirstOrder.Semiterm LX ξ n) :
    unTerm (.func (Sum.inl f) v) = .func f (fun i => unTerm (v i)) := rfl

/-- **`unTerm` commutes with rewriting**, given the two maps agree on bound and
free variables. -/
theorem unTerm_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} {ω : FirstOrder.Rew LX ξ₁ n₁ ξ₂ n₂}
    {ω' : FirstOrder.Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂}
    (hb : ∀ i, unTerm (ω (#i)) = ω' (#i)) (hf : ∀ x, unTerm (ω (&x)) = ω' (&x)) :
    ∀ (t : FirstOrder.Semiterm LX ξ₁ n₁), unTerm (ω t) = ω' (unTerm t)
  | .bvar i => hb i
  | .fvar x => hf x
  | .func (Sum.inl f) v => by
      have e1 : ω (FirstOrder.Semiterm.func (Sum.inl f) v) =
          FirstOrder.Semiterm.func (Sum.inl f) (fun i => ω (v i)) := ω.func (Sum.inl f) v
      have e2 : ω' (FirstOrder.Semiterm.func f (fun i => unTerm (v i))) =
          FirstOrder.Semiterm.func f (fun i => ω' (unTerm (v i))) :=
        ω'.func f (fun i => unTerm (v i))
      have e3 : unTerm (FirstOrder.Semiterm.func (Sum.inl f) v) =
          FirstOrder.Semiterm.func f (fun i => unTerm (v i)) := rfl
      calc unTerm (ω (FirstOrder.Semiterm.func (Sum.inl f) v))
          = unTerm (FirstOrder.Semiterm.func (Sum.inl f) (fun i => ω (v i))) := by rw [e1]
        _ = FirstOrder.Semiterm.func f (fun i => unTerm (ω (v i))) := rfl
        _ = FirstOrder.Semiterm.func f (fun i => ω' (unTerm (v i))) := by
              congr 1; funext i; exact unTerm_rew hb hf (v i)
        _ = ω' (FirstOrder.Semiterm.func f (fun i => unTerm (v i))) := e2.symm
        _ = ω' (unTerm (FirstOrder.Semiterm.func (Sum.inl f) v)) := by rw [e3]
  | .func (Sum.inr e) _ => e.elim

/-! ### The parametric lifting `toSOAtB ψ`

`ψ` carries no free number variable (`ξ := Empty`) so that `Rew.free`/
`Rew.shift` cannot renumber a variable of `ψ`'s own by mistake when they act
on the ambient formula around it — the substitution `ψ/[unTerm t]` is the only
place a number ever enters `ψ`.  Its set parameters live in its `N` bound set
slots (see the header). -/

variable {N : ℕ} {ψ : Semiformula ℒₒᵣ ℕ Empty N 1}

/-- **The parametric lifting.**  Every `LX`-atom not mentioning `X` is lifted
structurally (`lift`, composed with `unTerm` on the argument terms); `Xat t`
becomes `ψ` evaluated at `unTerm t`. -/
def toSOAtB {N : ℕ} (ψ : Semiformula ℒₒᵣ ℕ Empty N 1) {n : ℕ} :
    FirstOrder.Semiformula LX ℕ n → Semiformula ℒₒᵣ ℕ ℕ N n
  | .verum => ⊤
  | .falsum => ⊥
  | .rel (Sum.inl r) v => .rel r (fun i => unTerm (v i))
  | .rel (Sum.inr XRel.X) v => (FirstOrder.Rewriting.emb ψ)/[unTerm (v 0)]
  | .nrel (Sum.inl r) v => .nrel r (fun i => unTerm (v i))
  | .nrel (Sum.inr XRel.X) v => ∼((FirstOrder.Rewriting.emb ψ)/[unTerm (v 0)])
  | .and φ χ => toSOAtB ψ φ ⋏ toSOAtB ψ χ
  | .or φ χ => toSOAtB ψ φ ⋎ toSOAtB ψ χ
  | .all φ => ∀¹ (toSOAtB ψ φ)
  | .exs φ => ∃¹ (toSOAtB ψ φ)

/-- **The lifting at no set parameter** — the form `TI.lean` and `translate`
use, and the form every statement about `Provable` must be in (a `Proposition`
has `N = 0`). -/
abbrev toSOAt (ψ : Semiformula ℒₒᵣ ℕ Empty 0 1) {n : ℕ} :
    FirstOrder.Semiformula LX ℕ n → Semiproposition ℒₒᵣ 0 n := toSOAtB ψ

@[simp] theorem toSOAtB_verum {n : ℕ} : toSOAtB ψ (⊤ : FirstOrder.Semiformula LX ℕ n) = ⊤ := rfl

@[simp] theorem toSOAtB_falsum {n : ℕ} : toSOAtB ψ (⊥ : FirstOrder.Semiformula LX ℕ n) = ⊥ := rfl

@[simp] theorem toSOAtB_rel {n k : ℕ} (r : (ℒₒᵣ).Rel k) (v : Fin k → FirstOrder.Semiterm LX ℕ n) :
    toSOAtB ψ (.rel (Sum.inl r) v) = .rel r (fun i => unTerm (v i)) := rfl

@[simp] theorem toSOAtB_nrel {n k : ℕ} (r : (ℒₒᵣ).Rel k) (v : Fin k → FirstOrder.Semiterm LX ℕ n) :
    toSOAtB ψ (.nrel (Sum.inl r) v) = .nrel r (fun i => unTerm (v i)) := rfl

@[simp] theorem toSOAtB_Xat {n : ℕ} (t : FirstOrder.Semiterm LX ℕ n) :
    toSOAtB ψ (Xat t) = (FirstOrder.Rewriting.emb ψ)/[unTerm t] := rfl

@[simp] theorem toSOAtB_nXat {n : ℕ} (v : Fin 1 → FirstOrder.Semiterm LX ℕ n) :
    toSOAtB ψ (.nrel (Sum.inr XRel.X) v) = ∼((FirstOrder.Rewriting.emb ψ)/[unTerm (v 0)]) := rfl

@[simp] theorem toSOAtB_and {n : ℕ} (φ χ : FirstOrder.Semiformula LX ℕ n) :
    toSOAtB ψ (φ ⋏ χ) = toSOAtB ψ φ ⋏ toSOAtB ψ χ := rfl

@[simp] theorem toSOAtB_or {n : ℕ} (φ χ : FirstOrder.Semiformula LX ℕ n) :
    toSOAtB ψ (φ ⋎ χ) = toSOAtB ψ φ ⋎ toSOAtB ψ χ := rfl

@[simp] theorem toSOAtB_all {n : ℕ} (φ : FirstOrder.Semiformula LX ℕ (n + 1)) :
    toSOAtB ψ (∀¹ φ) = ∀¹ (toSOAtB ψ φ) := rfl

@[simp] theorem toSOAtB_exs {n : ℕ} (φ : FirstOrder.Semiformula LX ℕ (n + 1)) :
    toSOAtB ψ (∃¹ φ) = ∃¹ (toSOAtB ψ φ) := rfl

/-- **`toSOAtB` commutes with negation.** -/
@[simp] theorem toSOAtB_neg {n : ℕ} : ∀ (φ : FirstOrder.Semiformula LX ℕ n),
    toSOAtB ψ (∼φ) = ∼(toSOAtB ψ φ)
  | .verum => rfl
  | .falsum => rfl
  | .rel (Sum.inl _) _ => rfl
  | .rel (Sum.inr XRel.X) _ => rfl
  | .nrel (Sum.inl _) _ => rfl
  | .nrel (Sum.inr XRel.X) _ => (Semiformula.neg_neg _).symm
  | .and φ χ => by
      show toSOAtB ψ (∼φ) ⋎ toSOAtB ψ (∼χ) = ∼(toSOAtB ψ φ) ⋎ ∼(toSOAtB ψ χ)
      rw [toSOAtB_neg φ, toSOAtB_neg χ]
  | .or φ χ => by
      show toSOAtB ψ (∼φ) ⋏ toSOAtB ψ (∼χ) = ∼(toSOAtB ψ φ) ⋏ ∼(toSOAtB ψ χ)
      rw [toSOAtB_neg φ, toSOAtB_neg χ]
  | .all φ => by
      show ∃¹ (toSOAtB ψ (∼φ)) = ∃¹ (∼(toSOAtB ψ φ))
      rw [toSOAtB_neg φ]
  | .exs φ => by
      show ∀¹ (toSOAtB ψ (∼φ)) = ∀¹ (∼(toSOAtB ψ φ))
      rw [toSOAtB_neg φ]

/-- **`toSOAtB` commutes with implication** (`φ 🡒 χ` *is* `∼φ ⋎ χ`). -/
@[simp] theorem toSOAtB_imply {n : ℕ} (φ χ : FirstOrder.Semiformula LX ℕ n) :
    toSOAtB ψ (φ 🡒 χ) = toSOAtB ψ φ 🡒 toSOAtB ψ χ := by
  show toSOAtB ψ (∼φ ⋎ χ) = ∼(toSOAtB ψ φ) ⋎ toSOAtB ψ χ
  rw [toSOAtB_or, toSOAtB_neg]

/-- **A `toSOAtB`-image is arithmetical, provided `ψ` is.**  `ψ` only ever
enters through the atom `∼`/plain substitution `ψ/[t]`, never a fresh set
quantifier of its own, so no *new* second-order quantifier is introduced by
`toSOAtB` itself; but `ψ` can bring its own if it has one, hence the
hypothesis. -/
theorem arith_toSOAtB (hψ : Arith ψ) {n : ℕ} : ∀ (φ : FirstOrder.Semiformula LX ℕ n),
    Arith (toSOAtB ψ φ)
  | .verum => trivial
  | .falsum => trivial
  | .rel (Sum.inl _) _ => trivial
  | .rel (Sum.inr XRel.X) v => by
      show Arith ((FirstOrder.Rewriting.emb ψ)/[unTerm (v 0)])
      simp [hψ]
  | .nrel (Sum.inl _) _ => trivial
  | .nrel (Sum.inr XRel.X) v => by
      show Arith (∼((FirstOrder.Rewriting.emb ψ)/[unTerm (v 0)]))
      simp [hψ]
  | .and φ χ => ⟨arith_toSOAtB hψ φ, arith_toSOAtB hψ χ⟩
  | .or φ χ => ⟨arith_toSOAtB hψ φ, arith_toSOAtB hψ χ⟩
  | .all φ => arith_toSOAtB hψ φ
  | .exs φ => arith_toSOAtB hψ φ

/-- `arith_toSOAtB` at no set parameter (the form `TI.lean` uses). -/
theorem arith_toSOAt {ψ : Semiformula ℒₒᵣ ℕ Empty 0 1} (hψ : Arith ψ) {n : ℕ}
    (φ : FirstOrder.Semiformula LX ℕ n) : Arith (toSOAt ψ φ) :=
  arith_toSOAtB hψ φ

/-- **A `toSOAtB`-image has no free set variable, provided `ψ` has none.**  `ψ`'s
own set parameters are its *bound* slots, which `NoSetFvar` permits; this is
precisely what makes the image of `paLX`'s induction axiom an `ACA`-axiom. -/
theorem noSetFvar_toSOAtB
    (hψ : NoSetFvar (FirstOrder.Rewriting.emb ψ : Semiproposition ℒₒᵣ N 1)) {n : ℕ} :
    ∀ (φ : FirstOrder.Semiformula LX ℕ n), NoSetFvar (toSOAtB ψ φ)
  | .verum => trivial
  | .falsum => trivial
  | .rel (Sum.inl _) _ => trivial
  | .rel (Sum.inr XRel.X) v => by
      show NoSetFvar ((FirstOrder.Rewriting.emb ψ)/[unTerm (v 0)])
      simpa using hψ
  | .nrel (Sum.inl _) _ => trivial
  | .nrel (Sum.inr XRel.X) v => by
      show NoSetFvar (∼((FirstOrder.Rewriting.emb ψ)/[unTerm (v 0)]))
      simpa using hψ
  | .and φ χ => ⟨noSetFvar_toSOAtB hψ φ, noSetFvar_toSOAtB hψ χ⟩
  | .or φ χ => ⟨noSetFvar_toSOAtB hψ φ, noSetFvar_toSOAtB hψ χ⟩
  | .all φ => noSetFvar_toSOAtB hψ φ
  | .exs φ => noSetFvar_toSOAtB hψ φ

/-- A negated atom is the negation of the atom, on both sides of `toSOAtB`.
(`Semiformula.nrel r v` is *not* syntactically `∼(Semiformula.rel r v)`, so
`toSOAtB_neg` does not fire on it; this is the bridging equation the `identity`
case of `translate` needs.) -/
@[simp] theorem toSOAtB_nrel_neg {n k : ℕ} (r : LX.Rel k)
    (v : Fin k → FirstOrder.Semiterm LX ℕ n) :
    toSOAtB ψ (FirstOrder.Semiformula.nrel r v) =
      ∼(toSOAtB ψ (FirstOrder.Semiformula.rel r v)) :=
  toSOAtB_neg (FirstOrder.Semiformula.rel r v)

/-! ### `toSOAtB` commutes with rewriting

`ψ` has no free number variable of its own (`ξ := Empty`), so rewriting the
ambient formula never reaches inside `ψ` — it only moves the term `ψ` is
substituted at.  That is `emb_subst_rew`, and with it the whole commutation is
a structural induction. -/

theorem emb_subst_rew {M n₁ n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    (χ : Semiformula ℒₒᵣ ℕ Empty M 1) (u : FirstOrder.Semiterm ℒₒᵣ ℕ n₁) :
    ω ▹ ((FirstOrder.Rewriting.emb χ : Semiformula ℒₒᵣ ℕ ℕ M 1)/[u]) =
      (FirstOrder.Rewriting.emb χ : Semiformula ℒₒᵣ ℕ ℕ M 1)/[ω u] := by
  have he : (((ω.comp (FirstOrder.Rew.subst ![u])).comp FirstOrder.Rew.emb) :
        FirstOrder.Rew ℒₒᵣ Empty 1 ℕ n₂) =
      (FirstOrder.Rew.subst ![ω u]).comp FirstOrder.Rew.emb := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [FirstOrder.Rew.comp_app]
      | succ i => exact i.elim0
    · exact x.elim
  show ω ▹ (FirstOrder.Rew.subst ![u] ▹ (FirstOrder.Rew.emb ▹ χ)) =
    FirstOrder.Rew.subst ![ω u] ▹ (FirstOrder.Rew.emb ▹ χ)
  rw [← FirstOrder.TransitiveRewriting.comp_app, ← FirstOrder.TransitiveRewriting.comp_app,
    ← FirstOrder.TransitiveRewriting.comp_app, he]

theorem unTerm_bShift {ξ : Type*} {n : ℕ} (t : FirstOrder.Semiterm LX ξ n) :
    unTerm (FirstOrder.Rew.bShift t) = FirstOrder.Rew.bShift (unTerm t) :=
  unTerm_rew (fun _ => rfl) (fun _ => rfl) t

theorem q_hb {n₁ n₂ : ℕ} {ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂}
    {ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂} (hb : ∀ i, unTerm (ω #i) = ω' #i) :
    ∀ i, unTerm (ω.q #i) = ω'.q #i := by
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ j => simp [unTerm_bShift, hb j]

theorem q_hf {n₁ n₂ : ℕ} {ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂}
    {ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂} (hf : ∀ x, unTerm (ω &x) = ω' &x) :
    ∀ x, unTerm (ω.q &x) = ω'.q &x := by
  intro x
  simp [unTerm_bShift, hf x]

/-- **`toSOAtB` commutes with first-order rewriting**, given the two rewritings
agree on bound and free variables after erasing `X` from the terms. -/
theorem toSOAtB_rew : ∀ {n₁ n₂ : ℕ} {ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂}
    {ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂},
    (∀ i, unTerm (ω #i) = ω' #i) → (∀ x, unTerm (ω &x) = ω' &x) →
      ∀ (φ : FirstOrder.Semiformula LX ℕ n₁), toSOAtB ψ (ω ▹ φ) = ω' ▹ toSOAtB ψ φ
  | _, _, _,  _, _,  _, .verum => rfl
  | _, _, _,  _, _,  _, .falsum => rfl
  | _, _, ω, ω', hb, hf, .rel (Sum.inl r) v => by
      have h : ∀ i, unTerm (ω (v i)) = ω' (unTerm (v i)) := fun i => unTerm_rew hb hf (v i)
      show (Semiformula.rel r (fun i => unTerm (ω (v i))) : Semiformula ℒₒᵣ ℕ ℕ N _) =
        ω' ▹ (Semiformula.rel r (fun i => unTerm (v i)))
      rw [Semiformula.rew_rel]
      congr 1
      funext i
      exact h i
  | _, _, ω, ω', hb, hf, .nrel (Sum.inl r) v => by
      have h : ∀ i, unTerm (ω (v i)) = ω' (unTerm (v i)) := fun i => unTerm_rew hb hf (v i)
      show (Semiformula.nrel r (fun i => unTerm (ω (v i))) : Semiformula ℒₒᵣ ℕ ℕ N _) =
        ω' ▹ (Semiformula.nrel r (fun i => unTerm (v i)))
      rw [Semiformula.rew_nrel]
      congr 1
      funext i
      exact h i
  | _, _, ω, ω', hb, hf, .rel (Sum.inr XRel.X) v => by
      show (FirstOrder.Rewriting.emb ψ : Semiformula ℒₒᵣ ℕ ℕ N _)/[unTerm (ω (v 0))] =
        ω' ▹ ((FirstOrder.Rewriting.emb ψ : Semiformula ℒₒᵣ ℕ ℕ N _)/[unTerm (v 0)])
      rw [emb_subst_rew, unTerm_rew hb hf (v 0)]
  | _, _, ω, ω', hb, hf, .nrel (Sum.inr XRel.X) v => by
      show ∼((FirstOrder.Rewriting.emb ψ : Semiformula ℒₒᵣ ℕ ℕ N _)/[unTerm (ω (v 0))]) =
        ω' ▹ ∼((FirstOrder.Rewriting.emb ψ : Semiformula ℒₒᵣ ℕ ℕ N _)/[unTerm (v 0)])
      rw [LogicalConnective.HomClass.map_neg, emb_subst_rew, unTerm_rew hb hf (v 0)]
  | _, _, ω, ω', hb, hf, .and φ χ => by
      show toSOAtB ψ (ω ▹ φ) ⋏ toSOAtB ψ (ω ▹ χ) = ω' ▹ (toSOAtB ψ φ ⋏ toSOAtB ψ χ)
      rw [LogicalConnective.HomClass.map_and, toSOAtB_rew hb hf φ, toSOAtB_rew hb hf χ]
  | _, _, ω, ω', hb, hf, .or φ χ => by
      show toSOAtB ψ (ω ▹ φ) ⋎ toSOAtB ψ (ω ▹ χ) = ω' ▹ (toSOAtB ψ φ ⋎ toSOAtB ψ χ)
      rw [LogicalConnective.HomClass.map_or, toSOAtB_rew hb hf φ, toSOAtB_rew hb hf χ]
  | _, _, ω, ω', hb, hf, .all φ => by
      show ∀¹ (toSOAtB ψ (ω.q ▹ φ)) = ω' ▹ (∀¹ (toSOAtB ψ φ))
      rw [Semiformula.rew_all₀, toSOAtB_rew (q_hb hb) (q_hf hf) φ]
  | _, _, ω, ω', hb, hf, .exs φ => by
      show ∃¹ (toSOAtB ψ (ω.q ▹ φ)) = ω' ▹ (∃¹ (toSOAtB ψ φ))
      rw [Semiformula.rew_exs₀, toSOAtB_rew (q_hb hb) (q_hf hf) φ]

/-- **The `∀¹` rule's eigenvariable lemma.** -/
@[simp] theorem toSOAtB_free {n : ℕ} (φ : FirstOrder.Semiformula LX ℕ (n + 1)) :
    toSOAtB ψ (FirstOrder.Rewriting.free φ) = FirstOrder.Rewriting.free (toSOAtB ψ φ) :=
  toSOAtB_rew (ω := FirstOrder.Rew.free) (ω' := FirstOrder.Rew.free)
    (fun i => by cases i using Fin.lastCases <;> simp) (fun _ => by simp) φ

/-- **The `∀¹` rule's context lemma.** -/
@[simp] theorem toSOAtB_shift {n : ℕ} (φ : FirstOrder.Semiformula LX ℕ n) :
    toSOAtB ψ (FirstOrder.Rewriting.shift φ) = FirstOrder.Rewriting.shift (toSOAtB ψ φ) :=
  toSOAtB_rew (ω := FirstOrder.Rew.shift) (ω' := FirstOrder.Rew.shift)
    (fun _ => by simp) (fun _ => by simp) φ

/-- **The `∃¹` rule's substitution lemma.** -/
@[simp] theorem toSOAtB_subst₁ {n : ℕ} (φ : FirstOrder.Semiformula LX ℕ 1)
    (t : FirstOrder.Semiterm LX ℕ n) :
    toSOAtB ψ (φ/[t]) = (toSOAtB ψ φ)/[unTerm t] :=
  toSOAtB_rew (ω := FirstOrder.Rew.subst ![t]) (ω' := FirstOrder.Rew.subst ![unTerm t])
    (fun i => by
      have h0 : i = 0 := Subsingleton.elim i 0
      subst h0; simp) (fun _ => by simp) φ

/-- **`toSOAtB` commutes with the universal closure.** -/
theorem toSOAtB_allClosure : ∀ {n : ℕ} (φ : FirstOrder.Semiformula LX ℕ n),
    toSOAtB ψ (∀¹* φ) = ∀¹* (toSOAtB ψ φ)
  |       0, _ => rfl
  | (_n + 1), φ => toSOAtB_allClosure (∀¹ φ)

/-! ### Images of the purely arithmetical fragment

`toLX` embeds `ℒₒᵣ` into `LX` by tagging every symbol `Sum.inl`; `unTerm` and
`toSOAtB` undo exactly that, so the image of a purely arithmetical formula is
its `lift`, whatever `ψ` is.  This is what identifies the `toSOAtB`-image of
`Theory.lMap toLX 𝗣𝗔⁻` with `paMinus` ⊆ `ACA₀`. -/

@[simp] theorem unTerm_lMap {ξ : Type*} {n : ℕ} :
    ∀ (t : FirstOrder.Semiterm ℒₒᵣ ξ n), unTerm (FirstOrder.Semiterm.lMap toLX t) = t
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .func f v => by
      show FirstOrder.Semiterm.func f
          (fun i => unTerm (FirstOrder.Semiterm.lMap toLX (v i))) = _
      congr 1
      funext i
      exact unTerm_lMap (v i)

@[simp] theorem toSOAtB_lMap {n : ℕ} :
    ∀ (φ : FirstOrder.Semiformula ℒₒᵣ ℕ n),
      toSOAtB ψ (FirstOrder.Semiformula.lMap toLX φ) = lift φ
  | .verum => rfl
  | .falsum => rfl
  | .rel r v => by
      show (Semiformula.rel r (fun i => unTerm (FirstOrder.Semiterm.lMap toLX (v i))) :
        Semiformula ℒₒᵣ ℕ ℕ N _) = Semiformula.rel r v
      congr 1
      funext i
      exact unTerm_lMap (v i)
  | .nrel r v => by
      show (Semiformula.nrel r (fun i => unTerm (FirstOrder.Semiterm.lMap toLX (v i))) :
        Semiformula ℒₒᵣ ℕ ℕ N _) = Semiformula.nrel r v
      congr 1
      funext i
      exact unTerm_lMap (v i)
  | .and φ χ => by
      show toSOAtB ψ (FirstOrder.Semiformula.lMap toLX φ) ⋏
        toSOAtB ψ (FirstOrder.Semiformula.lMap toLX χ) = lift φ ⋏ lift χ
      rw [toSOAtB_lMap φ, toSOAtB_lMap χ]
  | .or φ χ => by
      show toSOAtB ψ (FirstOrder.Semiformula.lMap toLX φ) ⋎
        toSOAtB ψ (FirstOrder.Semiformula.lMap toLX χ) = lift φ ⋎ lift χ
      rw [toSOAtB_lMap φ, toSOAtB_lMap χ]
  | .all φ => by
      show ∀¹ (toSOAtB ψ (FirstOrder.Semiformula.lMap toLX φ)) = ∀¹ (lift φ)
      rw [toSOAtB_lMap φ]
  | .exs φ => by
      show ∃¹ (toSOAtB ψ (FirstOrder.Semiformula.lMap toLX φ)) = ∃¹ (lift φ)
      rw [toSOAtB_lMap φ]

/-! ### Instantiating the bound set parameters

`toSOAtB ψ` puts `ψ`'s set parameters in bound slots; substituting witnesses
`Φ` for those slots afterwards is the same as lifting at the already
substituted `ψ`.  This is the bridge between the *closed* induction axiom
(which `ACA` contains) and the free-set-variable instance the design actually
uses — `Toolkit.lean`'s `specSets` supplies the middle step. -/

/-- The embedding of the number-free fragment, as a `Rew` on one bound
variable — the `map` parameter that turns a set substitution over `ξ = Empty`
into one over `ξ = ℕ`. -/
abbrev embRew : FirstOrder.Rew ℒₒᵣ Empty 1 ℕ 1 := FirstOrder.Rew.emb

private theorem so_map_q {N₁ N₂ : ℕ} (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ Empty) :
    (Ω.map embRew).q = Ω.q.map embRew := by
  ext X
  · cases X using Fin.cases with
    | zero => simp [SecondOrder.Rew.q]
    | succ Y => simp [SecondOrder.Rew.q, Semiformula.bmap_comm]
  · simp [SecondOrder.Rew.q, Semiformula.bmap_comm]

private theorem emb_comm_subst₁ {M n : ℕ} (χ : Semiformula ℒₒᵣ ℕ Empty M 1)
    (t : FirstOrder.Semiterm ℒₒᵣ Empty n) :
    ((FirstOrder.Rewriting.emb χ : Semiformula ℒₒᵣ ℕ ℕ M 1)/[FirstOrder.Rew.emb t]) =
      FirstOrder.Rewriting.emb (χ/[t]) := by
  have he : ((FirstOrder.Rew.subst ![FirstOrder.Rew.emb t]).comp FirstOrder.Rew.emb :
        FirstOrder.Rew ℒₒᵣ Empty 1 ℕ n) =
      FirstOrder.Rew.emb.comp (FirstOrder.Rew.subst ![t]) := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [FirstOrder.Rew.comp_app]
      | succ i => exact i.elim0
    · exact x.elim
  show FirstOrder.Rew.subst ![FirstOrder.Rew.emb t] ▹ (FirstOrder.Rew.emb ▹ χ) =
    FirstOrder.Rew.emb ▹ (FirstOrder.Rew.subst ![t] ▹ χ)
  rw [← FirstOrder.TransitiveRewriting.comp_app, ← FirstOrder.TransitiveRewriting.comp_app, he]

/-- **A second-order substitution commutes with the embedding of the number-free
fragment.** -/
theorem so_app_emb {N₁ N₂ : ℕ} (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ Empty) :
    ∀ {n : ℕ} (φ : Semiformula ℒₒᵣ ℕ Empty N₁ n),
      (Ω.map embRew).app (FirstOrder.Rewriting.emb φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) =
        (FirstOrder.Rewriting.emb (Ω.app φ) : Semiformula ℒₒᵣ ℕ ℕ N₂ n) := by
  intro n φ
  induction φ using Semiformula.rec' generalizing N₂ with
  | hRel r v => rfl
  | hNrel r v => rfl
  | hBvar X t =>
      show ((Ω.map embRew).bv X)/[FirstOrder.Rew.emb t] = _
      show (FirstOrder.Rew.emb ▹ Ω.bv X)/[FirstOrder.Rew.emb t] = _
      rw [emb_comm_subst₁]
      rfl
  | hNbvar X t =>
      show ∼((FirstOrder.Rew.emb ▹ Ω.bv X)/[FirstOrder.Rew.emb t]) = _
      rw [emb_comm_subst₁, ← LogicalConnective.HomClass.map_neg]
      rfl
  | hFvar X t =>
      show (FirstOrder.Rew.emb ▹ Ω.fv X)/[FirstOrder.Rew.emb t] = _
      rw [emb_comm_subst₁]
      rfl
  | hNfvar X t =>
      show ∼((FirstOrder.Rew.emb ▹ Ω.fv X)/[FirstOrder.Rew.emb t]) = _
      rw [emb_comm_subst₁, ← LogicalConnective.HomClass.map_neg]
      rfl
  | hVerum => rfl
  | hFalsum => rfl
  | hAnd φ χ ihφ ihχ => simp only [LogicalConnective.HomClass.map_and, ihφ, ihχ]
  | hOr φ χ ihφ ihχ => simp only [LogicalConnective.HomClass.map_or, ihφ, ihχ]
  | hAll₁ φ ih =>
      show ∀¹ ((Ω.map embRew).app (FirstOrder.Rew.emb.q ▹ φ)) = _
      rw [FirstOrder.Rew.q_emb, ih]
      show _ = FirstOrder.Rew.emb ▹ (∀¹ (Ω.app φ))
      rw [Semiformula.rew_all₀, FirstOrder.Rew.q_emb]
  | hExs₁ φ ih =>
      show ∃¹ ((Ω.map embRew).app (FirstOrder.Rew.emb.q ▹ φ)) = _
      rw [FirstOrder.Rew.q_emb, ih]
      show _ = FirstOrder.Rew.emb ▹ (∃¹ (Ω.app φ))
      rw [Semiformula.rew_exs₀, FirstOrder.Rew.q_emb]
  | hAll₂ φ ih =>
      show ∀² ((Ω.map embRew).q.app (FirstOrder.Rew.emb ▹ φ)) = _
      rw [so_map_q, ih]
      rfl
  | hExs₂ φ ih =>
      show ∃² ((Ω.map embRew).q.app (FirstOrder.Rew.emb ▹ φ)) = _
      rw [so_map_q, ih]
      rfl

/-- **Substituting the bound set parameters of a `toSOAtB`-image.**  Together
with `Toolkit.lean`'s `specSets` this recovers the free-set-variable instance of
an `ACA`-axiom from the closed axiom. -/
theorem subst₁_toSOAtB (Φ : Fin N → Semiformula ℒₒᵣ ℕ Empty 0 1) {n : ℕ} :
    ∀ (χ : FirstOrder.Semiformula LX ℕ n),
      Semiproposition.subst₁ (toSOAtB ψ χ) (fun i => FirstOrder.Rewriting.emb (Φ i)) =
        toSOAt (Semiproposition.subst₁ ψ Φ) χ
  | .verum => rfl
  | .falsum => rfl
  | .rel (Sum.inl _) _ => rfl
  | .nrel (Sum.inl _) _ => rfl
  | .rel (Sum.inr XRel.X) v => by
      have hΩ : (SecondOrder.Rew.subst (fun i => FirstOrder.Rewriting.emb (Φ i)) :
            SecondOrder.Rew ℒₒᵣ ℕ N ℕ 0 ℕ) =
          (SecondOrder.Rew.subst Φ).map embRew := by
        ext X
        · simp
        · show ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& X) = _
          simp
      show (SecondOrder.Rew.subst (fun i => FirstOrder.Rewriting.emb (Φ i))).app
          ((FirstOrder.Rewriting.emb ψ)/[unTerm (v 0)]) = _
      rw [SecondOrder.Rew.app_comm_subst, hΩ, so_app_emb]
      rfl
  | .nrel (Sum.inr XRel.X) v => by
      have hΩ : (SecondOrder.Rew.subst (fun i => FirstOrder.Rewriting.emb (Φ i)) :
            SecondOrder.Rew ℒₒᵣ ℕ N ℕ 0 ℕ) =
          (SecondOrder.Rew.subst Φ).map embRew := by
        ext X
        · simp
        · show ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& X) = _
          simp
      show (SecondOrder.Rew.subst (fun i => FirstOrder.Rewriting.emb (Φ i))).app
          (∼((FirstOrder.Rewriting.emb ψ)/[unTerm (v 0)])) = _
      rw [LogicalConnective.HomClass.map_neg, SecondOrder.Rew.app_comm_subst, hΩ, so_app_emb]
      rfl
  | .and φ χ => by
      show Semiproposition.subst₁ (toSOAtB ψ φ) _ ⋏ Semiproposition.subst₁ (toSOAtB ψ χ) _ = _
      rw [subst₁_toSOAtB Φ φ, subst₁_toSOAtB Φ χ]
      rfl
  | .or φ χ => by
      show Semiproposition.subst₁ (toSOAtB ψ φ) _ ⋎ Semiproposition.subst₁ (toSOAtB ψ χ) _ = _
      rw [subst₁_toSOAtB Φ φ, subst₁_toSOAtB Φ χ]
      rfl
  | .all φ => by
      show ∀¹ (Semiproposition.subst₁ (toSOAtB ψ φ) _) = _
      rw [subst₁_toSOAtB Φ φ]
      rfl
  | .exs φ => by
      show ∃¹ (Semiproposition.subst₁ (toSOAtB ψ φ) _) = _
      rw [subst₁_toSOAtB Φ φ]
      rfl

/-! ### Translating a derivation -/

/-- `cut` with the two contexts merged — Foundation's `cut` concatenates them,
ours needs them shared, so both premises are weakened first. -/
private def cutShared {φ : Proposition ℒₒᵣ} {Γ Δ : SecondOrder.Sequent ℒₒᵣ}
    (dp : Derivation (φ :: Γ)) (dn : Derivation (∼φ :: Δ)) : Derivation (Γ ++ Δ) :=
  Derivation.cut
    (Derivation.wk dp (by
      intro x hx; simp only [List.mem_cons, List.mem_append] at hx ⊢; tauto))
    (Derivation.wk dn (by
      intro x hx; simp only [List.mem_cons, List.mem_append] at hx ⊢; tauto))

/-- **The translation of a `paLX`-derivation into an `ACA`-derivation**, at the
parameter `ψ`.  Every rule maps to its namesake; only `cut` (Foundation
concatenates the two contexts, ours shares them) and `identity` (Foundation's
is atomic, ours is general) need anything beyond the commutation lemmas. -/
def translate (ψ : Semiformula ℒₒᵣ ℕ Empty 0 1) :
    {Γ : FirstOrder.Sequent LX} → FirstOrder.Derivation Γ → Derivation (Γ.map (toSOAt ψ))
  | _, .identity r v =>
      Derivation.cast
        (Derivation.identity (φ := toSOAt ψ (FirstOrder.Semiformula.rel r v))) (by simp)
  | _, .cut (φ := φ) (Γ := Γ) (Δ := Δ) dp dn =>
      Derivation.cast
        (cutShared (φ := toSOAt ψ φ) (Γ := Γ.map (toSOAt ψ)) (Δ := Δ.map (toSOAt ψ))
          (translate ψ dp)
          (Derivation.cast (translate ψ dn)
            (by simp only [List.map_cons, toSOAtB_neg])))
        (by simp)
  | _, .contraction d h => Derivation.wk (translate ψ d) (List.map_subset _ h)
  | _, .verum => Derivation.cast Derivation.verum (by simp)
  | _, .or d => Derivation.or (translate ψ d)
  | _, .and dp dq => Derivation.and (translate ψ dp) (translate ψ dq)
  | _, .all (φ := φ) (Γ := Γ) d =>
      Derivation.all₁ (Derivation.cast (translate ψ d) (by
        simp [FirstOrder.Rewriting.shifts, SecondOrder.Sequent.shift₀, List.map_map,
          Function.comp_def]))
  | _, .exs (φ := φ) (t := t) (Γ := Γ) d =>
      Derivation.exs₁ (t := unTerm t) (Derivation.cast (translate ψ d) (by simp))

end OrdinalAnalysis.ACA
