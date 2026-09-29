/-
  Slot and shape checks for the KPi station (`Language.lean`, `Delta0.lean`, `Theory.lean`),
  following `IDw/SlotCheck.lean`'s discipline: earlier stations had a real bug from a swapped
  slot, so every axiom is checked TWICE, against independent descriptions.

    1. **Syntactic, against Foundation's quote notation** (which does not use `ballAt`/`bexAt`
       or my de Bruijn bookkeeping): `subsetAt`, `eqAt`, `tranAt`, `infiniteAt`, `pairAx`,
       `unionAx`, and the bodies `sepBody φ`, `colBody φ` for GENERIC `φ` are `rfl` to
       `“∀ w, ∃ y, (∀ x ∈ y, x ∈ w ∧ !φ x) ∧ ∀ x ∈ w, !φ x → x ∈ y”` etc.
       (NB: `“x y. …”` numbers the FIRST binder `#0`, `“∀ x y, …”` is outermost-first.)
    2. **(Ad.3) shape**: `relAt #0 (bShift ▹ pairAx)`, `… unionAx` equal the B92 relativisations
       `∀a∈x ∀b∈x ∃c∈x …`; for GENERIC Δ₀ `φ`, `relAt u (sepBody φ)` and `relAt u (colBody φ)`
       bound exactly `∀w ∃y` (`∀w`, `∃y`, `∃w₁`) and leave the matrix alone.
    3. **Semantic unfolding** in an arbitrary structure `(M, r, P)` (`r` = `∈`, `P` = `Ad`):
       `Holds (extAx / ad1Ax / ad2Ax / limAx / pairAx / unionAx / foundAx φ / sepAx φ / colAx φ)`
       is *exactly* the corresponding B92 first-order statement, with `φ`'s slots read as
       `x = ![x]`, `(x,y) = ![x,y]`, parameters `f : ℕ → M`.  (Negative control done by hand:
       swapping `![x, y]` to `![y, x]` in `holds_colAx` makes the proof fail.)
-/
import OrdinalAnalysis.KPi.Theory

set_option autoImplicit false

namespace OrdinalAnalysis
namespace KPi
open LO LO.FirstOrder

/-! ### Foundation's quote notation: `“x y. …”` numbers the FIRST binder `#0`. -/

example : (subsetAt (#0 : Semiterm LAd Empty 2) #1) = “x y. ∀ z ∈ x, z ∈ y” := by rfl
example : (eqAt (#0 : Semiterm LAd Empty 2) #1) =
    “x y. (∀ z ∈ x, z ∈ y) ∧ (∀ z ∈ y, z ∈ x)” := by rfl
example : (tranAt (#0 : Semiterm LAd Empty 1)) = “u. ∀ x ∈ u, ∀ y ∈ x, y ∈ u” := by rfl
example : (infiniteAt (#0 : Semiterm LAd Empty 1)) =
    “u. (∃ x ∈ u, ∀ z ∈ x, z ∈ x) ∧ ∀ x ∈ u, ∃ y ∈ u, x ∈ y” := by rfl

example : pairAx = “∀ x y, ∃ z, x ∈ z ∧ y ∈ z” := by rfl
example : unionAx = “∀ x, ∃ z, ∀ y ∈ x, ∀ u ∈ y, u ∈ z” := by rfl

example (φ : Semiformula LAd ℕ 1) :
    sepBody φ = “∀ w, ∃ y, (∀ x ∈ y, x ∈ w ∧ !φ x) ∧ ∀ x ∈ w, !φ x → x ∈ y” := by rfl

example (φ : Semiformula LAd ℕ 2) :
    colBody φ = “∀ w, (∀ x ∈ w, ∃ y, !φ x y) → ∃ v, ∀ x ∈ w, ∃ y ∈ v, !φ x y” := by rfl

section q_bvar
variable {L : Language} {ξ₁ ξ₂ : Type*} {n₂ : ℕ}
@[simp] theorem q_bvar_one' {m : ℕ} (ω : Rew L ξ₁ (m + 1) ξ₂ n₂) :
    ω.q (#1 : Semiterm L ξ₁ (m + 2)) = Rew.bShift (ω #0) := ω.q_bvar_succ 0
@[simp] theorem q_bvar_two' {m : ℕ} (ω : Rew L ξ₁ (m + 2) ξ₂ n₂) :
    ω.q (#2 : Semiterm L ξ₁ (m + 3)) = Rew.bShift (ω #1) := ω.q_bvar_succ 1
@[simp] theorem q_bvar_three' {m : ℕ} (ω : Rew L ξ₁ (m + 3) ξ₂ n₂) :
    ω.q (#3 : Semiterm L ξ₁ (m + 4)) = Rew.bShift (ω #2) := ω.q_bvar_succ 2
end q_bvar

/-! ### (Ad.3) on (Pair) and (Union): `A^x` keeps the bounded quantifiers, bounds the rest -/

theorem ad3_pair_shape : relAt (#0 : Semiterm LAd Empty 1) (Rew.bShift ▹ pairAx) =
    “x. ∀ a ∈ x, ∀ b ∈ x, ∃ c ∈ x, a ∈ c ∧ b ∈ c” := by
  have h : (Rew.bShift ▹ pairAx : Semiformula LAd Empty 1) =
      ∀¹ (∀¹ (∃¹ (memAt #2 #0 ⋏ memAt #1 #0))) := by simp [pairAx, memAt]
  rw [h]; rfl

theorem ad3_union_shape : relAt (#0 : Semiterm LAd Empty 1) (Rew.bShift ▹ unionAx) =
    “x. ∀ a ∈ x, ∃ z ∈ x, ∀ y ∈ a, ∀ u ∈ y, u ∈ z” := by
  have h : (Rew.bShift ▹ unionAx : Semiformula LAd Empty 1) =
      ∀¹ (∃¹ (ballAt #1 (ballAt #0 (memAt #0 #2)))) := by
    simp [unionAx, ballAt, nmemAt, memAt]
  rw [h]; rfl

/-! ### (Ad.3) on (Δ₀-Sep) and (Δ₀-Col), for generic Δ₀ `φ` -/

theorem sepMat_isDelta0 {φ : Semiformula LAd ℕ 1} (hφ : IsDelta0 φ) : IsDelta0 (sepMat φ) :=
  IsDelta0.and (IsDelta0.ball _ (IsDelta0.and (IsDelta0.mem _ _) (hφ.subst₁ _)))
    (IsDelta0.ball _ (IsDelta0.imp (hφ.subst₁ _) (IsDelta0.mem _ _)))

/-- **(Sep)^u**: relativising the (parameter-closed) body of (Δ₀-Sep) bounds exactly `∀w`, `∃y`
and leaves the Δ₀ matrix untouched: `∀w∈u ∃y∈u [∀x∈y(x∈w ∧ φ) ∧ ∀x∈w(φ → x∈y)]`. -/
theorem relAt_sepBody {φ : Semiformula LAd ℕ 1} (hφ : IsDelta0 φ) (u : Semiterm LAd ℕ 0) :
    relAt u (sepBody φ) = ballAt u (bexAt (Rew.bShift u) (sepMat φ)) := by
  show ∀¹ (nmemAt #0 (Rew.bShift u) ⋎ (∃¹ (memAt #0 (Rew.bShift (Rew.bShift u)) ⋏
      relAt (Rew.bShift (Rew.bShift u)) (sepMat φ)))) = _
  rw [relAt_of_isDelta0 (sepMat_isDelta0 hφ)]
  rfl

/-- A universal quantifier whose range is not of the shape `#0 ∉ v ∨ B` is unrestricted, so it
is relativised: `(∀x ψ)^u = ∀x (x ∈ u → ψ^u)`. -/
theorem relAt_all_of_not_or_nmem {ξ : Type*} {n : ℕ} (u : Semiterm LAd ξ n)
    (ψ : Semiformula LAd ξ (n + 1))
    (h : ∀ (v : Fin 2 → Semiterm LAd ξ (n + 1)) B, ψ ≠ Semiformula.or (Semiformula.nrel AdRel.mem v) B) :
    relAt u (∀¹ ψ) = ∀¹ (nmemAt #0 (Rew.bShift u) ⋎ relAt (Rew.bShift u) ψ) := by
  match ψ, h with
  | .or (.nrel AdRel.mem v) B, h => exact absurd rfl (h v B)
  | .verum, _ => rfl
  | .falsum, _ => rfl
  | .rel _ _, _ => rfl
  | .nrel _ _, _ => rfl
  | .and _ _, _ => rfl
  | .or (.verum) _, _ => rfl
  | .or (.falsum) _, _ => rfl
  | .or (.rel _ _) _, _ => rfl
  | .or (.nrel AdRel.ad _) _, _ => rfl
  | .or (.and _ _) _, _ => rfl
  | .or (.or _ _) _, _ => rfl
  | .or (.all _) _, _ => rfl
  | .or (.exs _) _, _ => rfl
  | .all _, _ => rfl
  | .exs _, _ => rfl

/-- **(Col)^u**: relativising the body of (Δ₀-Col) bounds `∀w`, the antecedent's `∃y` and the
consequent's `∃w₁`, leaving the Δ₀ matrix and the restricted quantifiers alone:
`∀w∈u [ ∀x∈w ∃y∈u φ → ∃w₁∈u ∀x∈w ∃y∈w₁ φ ]`.  (The hypothesis `hne` says the antecedent's `∃y`
is not *accidentally* restricted, i.e. `φ` is not of the shape `y ∈ v ∧ B` — in that case B92's
purely syntactic `A^u` leaves that `∃y` alone, which is harmless once `u` is transitive.) -/
theorem relAt_colBody {φ : Semiformula LAd ℕ 2} (hφ : IsDelta0 φ)
    (hne : ∀ (v : Fin 2 → Semiterm LAd ℕ 3) B,
      ∼(φ ⇜ ![#1, #0]) ≠ Semiformula.or (Semiformula.nrel AdRel.mem v) B)
    (u : Semiterm LAd ℕ 0) :
    relAt u (colBody φ) =
      ballAt u (ballAt #0 (bexAt (Rew.bShift (Rew.bShift u)) (φ ⇜ ![#1, #0])) 🡒
        bexAt (Rew.bShift u) (ballAt #1 (bexAt #1 (φ ⇜ ![#1, #0])))) := by
  have hδ : IsDelta0 (φ ⇜ ![#1, #0] : Semiformula LAd ℕ 3) := hφ.subst _
  have hδ4 : IsDelta0 (φ ⇜ ![#1, #0] : Semiformula LAd ℕ 4) := hφ.subst _
  show ∀¹ (nmemAt #0 (Rew.bShift u) ⋎
    (relAt (Rew.bShift u) (bexAt #0 (∀¹ ∼(φ ⇜ ![#1, #0]))) ⋎
     relAt (Rew.bShift u) (∃¹ (ballAt #1 (bexAt #1 (φ ⇜ ![#1, #0])))))) = _
  have e : relAt (Rew.bShift u) (∃¹ (ballAt #1 (bexAt #1 (φ ⇜ ![#1, #0])))) =
      bexAt (Rew.bShift u) (relAt (Rew.bShift (Rew.bShift u))
        (ballAt #1 (bexAt #1 (φ ⇜ ![#1, #0])))) := rfl
  rw [relAt_bexAt, relAt_all_of_not_or_nmem _ _ hne, relAt_of_isDelta0 hδ.neg, e,
    relAt_ballAt, relAt_bexAt, relAt_of_isDelta0 hδ4]
  rfl

/-! ### Semantic unfolding of every axiom (the slot check proper) -/

section Semantics

variable {M : Type*}

/-- The `ℒ_Ad`-structure on `M` interpreting `∈` by `r` and `Ad` by `P`. -/
abbrev adStruc (r : M → M → Prop) (P : M → Prop) : Structure LAd M where
  func := fun _ f => Empty.elim f
  rel := fun _ R v => match R with
    | AdRel.mem => r (v 0) (v 1)
    | AdRel.ad => P (v 0)

variable (r : M → M → Prop) (P : M → Prop)

section eval
variable {ξ : Type*} {n : ℕ} (b : Fin n → M) (f : ξ → M)

@[simp] theorem eval_memAt (s t : Semiterm LAd ξ n) :
    Semiformula.Eval (s := adStruc r P) b f (memAt s t) ↔
      r (Semiterm.val (s := adStruc r P) b f s) (Semiterm.val (s := adStruc r P) b f t) :=
  Iff.rfl

@[simp] theorem eval_nmemAt (s t : Semiterm LAd ξ n) :
    Semiformula.Eval (s := adStruc r P) b f (nmemAt s t) ↔
      ¬ r (Semiterm.val (s := adStruc r P) b f s) (Semiterm.val (s := adStruc r P) b f t) :=
  Iff.rfl

@[simp] theorem eval_adAt (t : Semiterm LAd ξ n) :
    Semiformula.Eval (s := adStruc r P) b f (adAt t) ↔
      P (Semiterm.val (s := adStruc r P) b f t) :=
  Iff.rfl

@[simp] theorem eval_ballAt (t : Semiterm LAd ξ n) (φ : Semiformula LAd ξ (n + 1)) :
    Semiformula.Eval (s := adStruc r P) b f (ballAt t φ) ↔
      ∀ x, r x (Semiterm.val (s := adStruc r P) b f t) →
        Semiformula.Eval (s := adStruc r P) (x :> b) f φ := by
  simp [ballAt, imp_iff_not_or]

@[simp] theorem eval_bexAt (t : Semiterm LAd ξ n) (φ : Semiformula LAd ξ (n + 1)) :
    Semiformula.Eval (s := adStruc r P) b f (bexAt t φ) ↔
      ∃ x, r x (Semiterm.val (s := adStruc r P) b f t) ∧
        Semiformula.Eval (s := adStruc r P) (x :> b) f φ := by
  simp [bexAt]

@[simp] theorem eval_subsetAt (u v : Semiterm LAd ξ n) :
    Semiformula.Eval (s := adStruc r P) b f (subsetAt u v) ↔
      ∀ x, r x (Semiterm.val (s := adStruc r P) b f u) → r x (Semiterm.val (s := adStruc r P) b f v) := by
  simp [subsetAt]

@[simp] theorem eval_eqAt (u v : Semiterm LAd ξ n) :
    Semiformula.Eval (s := adStruc r P) b f (eqAt u v) ↔
      (∀ x, r x (Semiterm.val (s := adStruc r P) b f u) → r x (Semiterm.val (s := adStruc r P) b f v)) ∧
      (∀ x, r x (Semiterm.val (s := adStruc r P) b f v) → r x (Semiterm.val (s := adStruc r P) b f u)) := by
  simp [eqAt]

end eval

/-- "`σ` holds in `(M, r, P)`". -/
abbrev Holds (σ : Sentence LAd) : Prop := Semiformula.Eval (s := adStruc r P) ![] Empty.elim σ

theorem holds_pairAx : Holds r P pairAx ↔ ∀ x y, ∃ z, r x z ∧ r y z := by
  simp [Holds, pairAx]

theorem holds_unionAx : Holds r P unionAx ↔
    ∀ x, ∃ z, ∀ y, r y x → ∀ u, r u y → r u z := by
  simp [Holds, unionAx]

theorem holds_limAx : Holds r P limAx ↔ ∀ x, ∃ y, P y ∧ r x y := by
  simp [Holds, limAx]

theorem holds_extAx : Holds r P extAx ↔ ∀ x y z,
    ((∀ a, r a x → r a y) ∧ (∀ a, r a y → r a x)) → (r x z → r y z) ∧ (P x → P y) := by
  simp [Holds, extAx, imp_iff_not_or]

theorem holds_ad2Ax : Holds r P ad2Ax ↔ ∀ x y, P x ∧ P y →
    (r x y ∨ ((∀ a, r a x → r a y) ∧ (∀ a, r a y → r a x)) ∨ r y x) := by
  simp [Holds, ad2Ax, imp_iff_not_or]

theorem holds_ad1Ax : Holds r P ad1Ax ↔ ∀ x, P x →
    (∀ y, r y x → ∀ z, r z y → r z x) ∧
    ∃ w, r w x ∧ ((∃ a, r a w ∧ ∀ c, r c a → r c a) ∧ ∀ a, r a w → ∃ b, r b w ∧ r a b) := by
  simp [Holds, ad1Ax, tranAt, infiniteAt, subsetAt, imp_iff_not_or]

variable [Nonempty M]

theorem holds_foundAx (φ : Semiformula LAd ℕ 1) : Holds r P (foundAx φ) ↔ ∀ f : ℕ → M,
    (∀ x, (∀ y, r y x → Semiformula.Eval (s := adStruc r P) ![y] f φ) →
      Semiformula.Eval (s := adStruc r P) ![x] f φ) →
    ∀ x, Semiformula.Eval (s := adStruc r P) ![x] f φ := by
  simp [Holds, foundAx, foundBody, imp_iff_not_or]

theorem holds_sepAx (φ : Semiformula LAd ℕ 1) : Holds r P (sepAx φ) ↔ ∀ f : ℕ → M, ∀ w, ∃ y,
    (∀ x, r x y → r x w ∧ Semiformula.Eval (s := adStruc r P) ![x] f φ) ∧
    (∀ x, r x w → Semiformula.Eval (s := adStruc r P) ![x] f φ → r x y) := by
  simp [Holds, sepAx, sepBody, sepMat, imp_iff_not_or]

theorem holds_colAx (φ : Semiformula LAd ℕ 2) : Holds r P (colAx φ) ↔ ∀ f : ℕ → M, ∀ w,
    (∀ x, r x w → ∃ y, Semiformula.Eval (s := adStruc r P) ![x, y] f φ) →
    ∃ v, ∀ x, r x w → ∃ y, r y v ∧ Semiformula.Eval (s := adStruc r P) ![x, y] f φ := by
  simp [Holds, colAx, colBody, imp_iff_not_or]

end Semantics

end KPi

end OrdinalAnalysis
