module

public import OrdinalAnalysis.KPi.SlotCheck

@[expose] public section

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.Sound

open LO LO.FirstOrder

variable {M : Type*} (r : M → M → Prop) (P : M → Prop)

/-- Guarded evaluation: like `Semiformula.Eval` in `adStruc r P`, except that every quantifier
ranges over the guard `D` only. -/
def EvalG (D : M → Prop) {ξ : Type*} : {n : ℕ} → (Fin n → M) → (ξ → M) → Semiformula LAd ξ n → Prop
  | _, _, _, .verum => True
  | _, _, _, .falsum => False
  | _, b, f, .rel R v => (adStruc r P).rel R (fun i => Semiterm.val (s := adStruc r P) b f (v i))
  | _, b, f, .nrel R v => ¬ (adStruc r P).rel R (fun i => Semiterm.val (s := adStruc r P) b f (v i))
  | _, b, f, .and φ ψ => EvalG D b f φ ∧ EvalG D b f ψ
  | _, b, f, .or φ ψ => EvalG D b f φ ∨ EvalG D b f ψ
  | _, b, f, .all φ => ∀ y, D y → EvalG D (y :> b) f φ
  | _, b, f, .exs φ => ∃ y, D y ∧ EvalG D (y :> b) f φ

section EvalG

variable {ξ : Type*} {n : ℕ} (D : M → Prop) (b : Fin n → M) (f : ξ → M)

@[simp] theorem evalG_and (φ ψ : Semiformula LAd ξ n) :
    EvalG r P D b f (φ ⋏ ψ) ↔ EvalG r P D b f φ ∧ EvalG r P D b f ψ := Iff.rfl

@[simp] theorem evalG_or (φ ψ : Semiformula LAd ξ n) :
    EvalG r P D b f (φ ⋎ ψ) ↔ EvalG r P D b f φ ∨ EvalG r P D b f ψ := Iff.rfl

@[simp] theorem evalG_verum : EvalG r P D b f (⊤ : Semiformula LAd ξ n) ↔ True := Iff.rfl

@[simp] theorem evalG_falsum : EvalG r P D b f (⊥ : Semiformula LAd ξ n) ↔ False := Iff.rfl

@[simp] theorem evalG_all (φ : Semiformula LAd ξ (n + 1)) :
    EvalG r P D b f (∀¹ φ) ↔ ∀ y, D y → EvalG r P D (y :> b) f φ := Iff.rfl

@[simp] theorem evalG_exs (φ : Semiformula LAd ξ (n + 1)) :
    EvalG r P D b f (∃¹ φ) ↔ ∃ y, D y ∧ EvalG r P D (y :> b) f φ := Iff.rfl

@[simp] theorem evalG_memAt (s t : Semiterm LAd ξ n) :
    EvalG r P D b f (memAt s t) ↔
      r (Semiterm.val (s := adStruc r P) b f s) (Semiterm.val (s := adStruc r P) b f t) := Iff.rfl

@[simp] theorem evalG_nmemAt (s t : Semiterm LAd ξ n) :
    EvalG r P D b f (nmemAt s t) ↔
      ¬ r (Semiterm.val (s := adStruc r P) b f s) (Semiterm.val (s := adStruc r P) b f t) := Iff.rfl

@[simp] theorem evalG_adAt (t : Semiterm LAd ξ n) :
    EvalG r P D b f (adAt t) ↔ P (Semiterm.val (s := adStruc r P) b f t) := Iff.rfl

@[simp] theorem evalG_nadAt (t : Semiterm LAd ξ n) :
    EvalG r P D b f (nadAt t) ↔ ¬ P (Semiterm.val (s := adStruc r P) b f t) := Iff.rfl

theorem evalG_ballAt (t : Semiterm LAd ξ n) (φ : Semiformula LAd ξ (n + 1)) :
    EvalG r P D b f (ballAt t φ) ↔
      ∀ y, D y → r y (Semiterm.val (s := adStruc r P) b f t) → EvalG r P D (y :> b) f φ := by
  unfold ballAt
  rw [evalG_all]
  refine forall_congr' fun y => imp_congr_right fun _ => ?_
  simp [imp_iff_not_or]

theorem evalG_bexAt (t : Semiterm LAd ξ n) (φ : Semiformula LAd ξ (n + 1)) :
    EvalG r P D b f (bexAt t φ) ↔
      ∃ y, D y ∧ r y (Semiterm.val (s := adStruc r P) b f t) ∧ EvalG r P D (y :> b) f φ := by
  unfold bexAt
  rw [evalG_exs]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  simp

end EvalG

/-! ### Rewriting -/

section Rew

variable {ξ₁ ξ₂ : Type*} (D : M → Prop)

theorem env_q {n₁ n₂ : ℕ} (ω : Rew LAd ξ₁ n₁ ξ₂ n₂) (y : M) (b₂ : Fin n₂ → M) (f₂ : ξ₂ → M) :
    (Semiterm.val (s := adStruc r P) (y :> b₂) f₂ ∘ ω.q ∘ Semiterm.bvar) =
        (y :> (Semiterm.val (s := adStruc r P) b₂ f₂ ∘ ω ∘ Semiterm.bvar)) ∧
      (Semiterm.val (s := adStruc r P) (y :> b₂) f₂ ∘ ω.q ∘ Semiterm.fvar) =
        (Semiterm.val (s := adStruc r P) b₂ f₂ ∘ ω ∘ Semiterm.fvar) := by
  constructor
  · funext i; cases i using Fin.cases <;> simp [Function.comp_def]
  · funext i; simp [Function.comp_def]

theorem evalG_rew {n₁ n₂ : ℕ} (ω : Rew LAd ξ₁ n₁ ξ₂ n₂) (φ : Semiformula LAd ξ₁ n₁)
    (b₂ : Fin n₂ → M) (f₂ : ξ₂ → M) :
    EvalG r P D b₂ f₂ (ω ▹ φ) ↔
      EvalG r P D (Semiterm.val (s := adStruc r P) b₂ f₂ ∘ ω ∘ Semiterm.bvar)
        (Semiterm.val (s := adStruc r P) b₂ f₂ ∘ ω ∘ Semiterm.fvar) φ := by
  match φ with
  | .rel R v | .nrel R v =>
    simp only [Semiformula.rew_rel_eq_comp, Semiformula.rew_nrel_eq_comp]
    apply iff_of_eq
    simp only [EvalG]
    congr 2 <;> funext i <;> simp [Semiterm.val_rew]
  | ⊤ | ⊥ => simp
  | φ ⋏ ψ | φ ⋎ ψ => simp [evalG_rew ω φ, evalG_rew ω ψ]
  | ∀¹ φ =>
    have e : ω ▹ (∀¹ φ) = ∀¹ (ω.q ▹ φ) := rfl
    rw [e, evalG_all]
    refine forall_congr' fun y => imp_congr_right fun _ => ?_
    rw [evalG_rew ω.q φ, (env_q r P ω y b₂ f₂).1, (env_q r P ω y b₂ f₂).2]
  | ∃¹ φ =>
    have e : ω ▹ (∃¹ φ) = ∃¹ (ω.q ▹ φ) := rfl
    rw [e, evalG_exs]
    refine exists_congr fun y => and_congr_right fun _ => ?_
    rw [evalG_rew ω.q φ, (env_q r P ω y b₂ f₂).1, (env_q r P ω y b₂ f₂).2]

end Rew

theorem evalG_bShift {ξ : Type*} {n : ℕ} (D : M → Prop) (y : M) (b : Fin n → M) (f : ξ → M)
    (φ : Semiformula LAd ξ n) :
    EvalG r P D (y :> b) f (Rew.bShift ▹ φ) ↔ EvalG r P D b f φ := by
  rw [evalG_rew]
  have h1 : (Semiterm.val (s := adStruc r P) (y :> b) f ∘ (Rew.bShift : Rew LAd ξ n ξ (n + 1)) ∘
      Semiterm.bvar) = b := by
    funext i; simp [Function.comp_def]
  have h2 : (Semiterm.val (s := adStruc r P) (y :> b) f ∘ (Rew.bShift : Rew LAd ξ n ξ (n + 1)) ∘
      Semiterm.fvar) = f := by
    funext i; simp [Function.comp_def]
  rw [h1, h2]

/-! ### The relativisation lemma -/

section RelAt

variable {ξ : Type*} {n : ℕ}

theorem isBv0_eq {t : Semiterm LAd ξ (n + 1)} (h : isBv0 t = true) : t = #0 := by
  cases t with
  | bvar i =>
    have : i = 0 := by simpa [isBv0] using h
    subst this; rfl
  | fvar x => simp [isBv0] at h
  | func f _ => exact Empty.elim f

theorem isBv0_false_exists {t : Semiterm LAd ξ (n + 1)} (h : isBv0 t = false) :
    ∃ t' : Semiterm LAd ξ n, t = Rew.bShift t' := by
  cases t with
  | bvar i =>
    have hi : i ≠ 0 := by simpa [isBv0] using h
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
    exact ⟨#j, by simp⟩
  | fvar x => exact ⟨&x, by simp⟩
  | func f _ => exact Empty.elim f

theorem relAt_all_restr (u : Semiterm LAd ξ n) (v : Fin 2 → Semiterm LAd ξ (n + 1))
    (B : Semiformula LAd ξ (n + 1)) (hc : (isBv0 (v 0) && !isBv0 (v 1)) = true) :
    relAt u (∀¹ (Semiformula.or (Semiformula.nrel AdRel.mem v) B)) =
      ∀¹ (Semiformula.nrel AdRel.mem v ⋎ relAt (Rew.bShift u) B) :=
  (if_pos hc).trans rfl

theorem relAt_all_gen (u : Semiterm LAd ξ n) (ψ : Semiformula LAd ξ (n + 1))
    (hs : ¬ ∃ (v : Fin 2 → Semiterm LAd ξ (n + 1)) (B : Semiformula LAd ξ (n + 1)),
      ψ = Semiformula.or (Semiformula.nrel AdRel.mem v) B ∧
        (isBv0 (v 0) && !isBv0 (v 1)) = true) :
    relAt u (∀¹ ψ) = ∀¹ (nmemAt #0 (Rew.bShift u) ⋎ relAt (Rew.bShift u) ψ) := by
  match ψ, hs with
  | .or (.nrel AdRel.mem v) B, hs =>
    have hc : ¬ ((isBv0 (v 0) && !isBv0 (v 1)) = true) := fun hc => hs ⟨v, B, rfl, hc⟩
    exact (if_neg hc).trans rfl
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

theorem relAt_exs_restr (u : Semiterm LAd ξ n) (v : Fin 2 → Semiterm LAd ξ (n + 1))
    (B : Semiformula LAd ξ (n + 1)) (hc : (isBv0 (v 0) && !isBv0 (v 1)) = true) :
    relAt u (∃¹ (Semiformula.and (Semiformula.rel AdRel.mem v) B)) =
      ∃¹ (Semiformula.rel AdRel.mem v ⋏ relAt (Rew.bShift u) B) :=
  (if_pos hc).trans rfl

theorem relAt_exs_gen (u : Semiterm LAd ξ n) (ψ : Semiformula LAd ξ (n + 1))
    (hs : ¬ ∃ (v : Fin 2 → Semiterm LAd ξ (n + 1)) (B : Semiformula LAd ξ (n + 1)),
      ψ = Semiformula.and (Semiformula.rel AdRel.mem v) B ∧
        (isBv0 (v 0) && !isBv0 (v 1)) = true) :
    relAt u (∃¹ ψ) = ∃¹ (memAt #0 (Rew.bShift u) ⋏ relAt (Rew.bShift u) ψ) := by
  match ψ, hs with
  | .and (.rel AdRel.mem v) B, hs =>
    have hc : ¬ ((isBv0 (v 0) && !isBv0 (v 1)) = true) := fun hc => hs ⟨v, B, rfl, hc⟩
    exact (if_neg hc).trans rfl
  | .verum, _ => rfl
  | .falsum, _ => rfl
  | .rel _ _, _ => rfl
  | .nrel _ _, _ => rfl
  | .or _ _, _ => rfl
  | .and (.verum) _, _ => rfl
  | .and (.falsum) _, _ => rfl
  | .and (.rel AdRel.ad _) _, _ => rfl
  | .and (.nrel _ _) _, _ => rfl
  | .and (.and _ _) _, _ => rfl
  | .and (.or _ _) _, _ => rfl
  | .and (.all _) _, _ => rfl
  | .and (.exs _) _, _ => rfl
  | .all _, _ => rfl
  | .exs _, _ => rfl

end RelAt

/-! ### Plumbing: `Eval` / `EvalG` of connectives and memberships (all `Iff.rfl`) -/

section Plumb

variable {ξ : Type*} {n : ℕ} (b : Fin n → M) (f : ξ → M)

theorem eval_or' (φ ψ : Semiformula LAd ξ n) :
    Semiformula.Eval (s := adStruc r P) b f (φ ⋎ ψ) ↔
      Semiformula.Eval (s := adStruc r P) b f φ ∨ Semiformula.Eval (s := adStruc r P) b f ψ :=
  Iff.rfl

theorem eval_and' (φ ψ : Semiformula LAd ξ n) :
    Semiformula.Eval (s := adStruc r P) b f (φ ⋏ ψ) ↔
      Semiformula.Eval (s := adStruc r P) b f φ ∧ Semiformula.Eval (s := adStruc r P) b f ψ :=
  Iff.rfl

theorem eval_all' (φ : Semiformula LAd ξ (n + 1)) :
    Semiformula.Eval (s := adStruc r P) b f (∀¹ φ) ↔
      ∀ y : M, Semiformula.Eval (s := adStruc r P) (y :> b) f φ :=
  Iff.rfl

theorem eval_exs' (φ : Semiformula LAd ξ (n + 1)) :
    Semiformula.Eval (s := adStruc r P) b f (∃¹ φ) ↔
      ∃ y : M, Semiformula.Eval (s := adStruc r P) (y :> b) f φ :=
  Iff.rfl

theorem eval_nrelmem (v : Fin 2 → Semiterm LAd ξ n) :
    Semiformula.Eval (s := adStruc r P) b f (Semiformula.nrel AdRel.mem v) ↔
      ¬ r (Semiterm.val (s := adStruc r P) b f (v 0)) (Semiterm.val (s := adStruc r P) b f (v 1)) :=
  Iff.rfl

theorem eval_relmem (v : Fin 2 → Semiterm LAd ξ n) :
    Semiformula.Eval (s := adStruc r P) b f (Semiformula.rel AdRel.mem v) ↔
      r (Semiterm.val (s := adStruc r P) b f (v 0)) (Semiterm.val (s := adStruc r P) b f (v 1)) :=
  Iff.rfl

theorem evalG_nrelmem (D : M → Prop) (v : Fin 2 → Semiterm LAd ξ n) :
    EvalG r P D b f (Semiformula.nrel AdRel.mem v) ↔
      ¬ r (Semiterm.val (s := adStruc r P) b f (v 0)) (Semiterm.val (s := adStruc r P) b f (v 1)) :=
  Iff.rfl

theorem evalG_relmem (D : M → Prop) (v : Fin 2 → Semiterm LAd ξ n) :
    EvalG r P D b f (Semiformula.rel AdRel.mem v) ↔
      r (Semiterm.val (s := adStruc r P) b f (v 0)) (Semiterm.val (s := adStruc r P) b f (v 1)) :=
  Iff.rfl

theorem evalG_or_nrelmem (D : M → Prop) (v : Fin 2 → Semiterm LAd ξ n) (B : Semiformula LAd ξ n) :
    EvalG r P D b f (Semiformula.or (Semiformula.nrel AdRel.mem v) B) ↔
      (¬ r (Semiterm.val (s := adStruc r P) b f (v 0)) (Semiterm.val (s := adStruc r P) b f (v 1)) ∨
        EvalG r P D b f B) :=
  Iff.rfl

theorem evalG_and_relmem (D : M → Prop) (v : Fin 2 → Semiterm LAd ξ n) (B : Semiformula LAd ξ n) :
    EvalG r P D b f (Semiformula.and (Semiformula.rel AdRel.mem v) B) ↔
      (r (Semiterm.val (s := adStruc r P) b f (v 0)) (Semiterm.val (s := adStruc r P) b f (v 1)) ∧
        EvalG r P D b f B) :=
  Iff.rfl

theorem eval_imp_adAt (t : Semiterm LAd ξ n) (X : Semiformula LAd ξ n) :
    Semiformula.Eval (s := adStruc r P) b f (adAt t 🡒 X) ↔
      (P (Semiterm.val (s := adStruc r P) b f t) → Semiformula.Eval (s := adStruc r P) b f X) := by
  have e : (adAt t 🡒 X) = (nadAt t ⋎ X) := rfl
  rw [e, eval_or']
  exact imp_iff_not_or.symm

theorem val_bvar_zero {m : ℕ} (y : M) (b' : Fin m → M) :
    Semiterm.val (s := adStruc r P) (y :> b') f (#0 : Semiterm LAd ξ (m + 1)) = y := by
  simp

end Plumb

section RelAtEval

variable {ξ : Type*}

/-- **Relativisation lemma.**  Let `x` be an element and `D` a guard with `r y x ↔ D y`; `Q` is an
invariant on environment values (`D` or `x`), such that `r y c → D y` whenever `Q c`.  Then, for
a term `u` with value `x`, evaluating `A^u` in `(M, r, P)` is the same as evaluating `A` with all
quantifiers guarded by `D`. -/
theorem eval_relAt_iff (D Q : M → Prop) (x : M) (hDx : ∀ y, r y x ↔ D y)
    (hQD : ∀ y, D y → Q y) (hT : ∀ c, Q c → ∀ y, r y c → D y) {n : ℕ}
    (φ : Semiformula LAd ξ n) :
    ∀ (u : Semiterm LAd ξ n) (b : Fin n → M) (f : ξ → M), (∀ i, Q (b i)) → (∀ i, Q (f i)) →
      Semiterm.val (s := adStruc r P) b f u = x →
      (Semiformula.Eval (s := adStruc r P) b f (relAt u φ) ↔ EvalG r P D b f φ) := by
  induction φ with
  | verum => intro u b f _ _ _; exact Iff.rfl
  | falsum => intro u b f _ _ _; exact Iff.rfl
  | rel R v => intro u b f _ _ _; exact Iff.rfl
  | nrel R v => intro u b f _ _ _; exact Iff.rfl
  | and φ ψ ihφ ihψ =>
    intro u b f hb hf hu
    exact and_congr (ihφ u b f hb hf hu) (ihψ u b f hb hf hu)
  | or φ ψ ihφ ihψ =>
    intro u b f hb hf hu
    exact or_congr (ihφ u b f hb hf hu) (ihψ u b f hb hf hu)
  | all ψ ih =>
    intro u b f hb hf hu
    change Semiformula.Eval (s := adStruc r P) b f (relAt u (∀¹ ψ)) ↔ EvalG r P D b f (∀¹ ψ)
    have hu' : ∀ y : M, Semiterm.val (s := adStruc r P) (y :> b) f (Rew.bShift u) = x :=
      fun y => by simpa using hu
    have hb' : ∀ y, Q y → ∀ i, Q ((y :> b) i) := fun y hy i => by
      cases i using Fin.cases <;> simp [hy, hb]
    by_cases hs : ∃ (v : Fin 2 → Semiterm LAd ξ (_ + 1)) (B : Semiformula LAd ξ (_ + 1)),
      ψ = Semiformula.or (Semiformula.nrel AdRel.mem v) B ∧
        (isBv0 (v 0) && !isBv0 (v 1)) = true
    · obtain ⟨v, B, rfl, hc⟩ := hs
      rw [relAt_all_restr u v B hc, eval_all', evalG_all]
      have hc' := Bool.and_eq_true_iff.mp hc
      have h0 : v 0 = #0 := isBv0_eq hc'.1
      obtain ⟨t', ht'⟩ := isBv0_false_exists (t := v 1) (by simpa using hc'.2)
      have hct : Q (Semiterm.val (s := adStruc r P) b f t') := by
        cases t' with
        | bvar i => exact hb i
        | fvar i => exact hf i
        | func F _ => exact Empty.elim F
      have e0 : ∀ y, Semiterm.val (s := adStruc r P) (y :> b) f (v 0) = y := fun y => by
        simp [h0]
      have e1 : ∀ y, Semiterm.val (s := adStruc r P) (y :> b) f (v 1) =
          Semiterm.val (s := adStruc r P) b f t' := fun y => by simp [ht']
      have hN : ∀ y, Semiformula.Eval (s := adStruc r P) (y :> b) f
          (Semiformula.nrel AdRel.mem v) ↔ ¬ r y (Semiterm.val (s := adStruc r P) b f t') :=
        fun y => by rw [eval_nrelmem, e0, e1]
      have hNG : ∀ y, EvalG r P D (y :> b) f (Semiformula.nrel AdRel.mem v) ↔
          ¬ r y (Semiterm.val (s := adStruc r P) b f t') :=
        fun y => by rw [evalG_nrelmem, e0, e1]
      have key : ∀ y, r y (Semiterm.val (s := adStruc r P) b f t') →
          (Semiformula.Eval (s := adStruc r P) (y :> b) f (relAt (Rew.bShift u) B) ↔
            EvalG r P D (y :> b) f B) := by
        intro y hry
        have hDy := hT _ hct y hry
        have this : (Semiformula.Eval (s := adStruc r P) (y :> b) f (Semiformula.nrel AdRel.mem v) ∨
            Semiformula.Eval (s := adStruc r P) (y :> b) f (relAt (Rew.bShift u) B)) ↔
            (EvalG r P D (y :> b) f (Semiformula.nrel AdRel.mem v) ∨
              EvalG r P D (y :> b) f B) :=
          ih (Rew.bShift u) (y :> b) f (hb' y (hQD y hDy)) hf (hu' y)
        rw [hN, hNG] at this
        constructor
        · intro h
          rcases this.mp (Or.inr h) with h' | h'
          · exact absurd hry h'
          · exact h'
        · intro h
          rcases this.mpr (Or.inr h) with h' | h'
          · exact absurd hry h'
          · exact h'
      refine forall_congr' fun y => ?_
      rw [eval_or', hN, evalG_or_nrelmem, e0, e1]
      by_cases hry : r y (Semiterm.val (s := adStruc r P) b f t')
      · have hDy := hT _ hct y hry
        constructor
        · intro h _; exact Or.inr ((key y hry).mp (h.resolve_left (not_not.mpr hry)))
        · intro h; exact Or.inr ((key y hry).mpr ((h hDy).resolve_left (not_not.mpr hry)))
      · exact ⟨fun _ _ => Or.inl hry, fun _ => Or.inl hry⟩
    · rw [relAt_all_gen u ψ hs, eval_all', evalG_all]
      refine forall_congr' fun y => ?_
      rw [eval_or', eval_nmemAt, val_bvar_zero, hu' y]
      constructor
      · intro h hDy
        have := ih (Rew.bShift u) (y :> b) f (hb' y (hQD y hDy)) hf (hu' y)
        rcases h with h | h
        · exact absurd ((hDx y).mpr hDy) h
        · exact this.mp h
      · intro h
        by_cases hry : r y x
        · have hDy := (hDx y).mp hry
          have := ih (Rew.bShift u) (y :> b) f (hb' y (hQD y hDy)) hf (hu' y)
          exact Or.inr (this.mpr (h hDy))
        · exact Or.inl hry
  | exs ψ ih =>
    intro u b f hb hf hu
    change Semiformula.Eval (s := adStruc r P) b f (relAt u (∃¹ ψ)) ↔ EvalG r P D b f (∃¹ ψ)
    have hu' : ∀ y : M, Semiterm.val (s := adStruc r P) (y :> b) f (Rew.bShift u) = x :=
      fun y => by simpa using hu
    have hb' : ∀ y, Q y → ∀ i, Q ((y :> b) i) := fun y hy i => by
      cases i using Fin.cases <;> simp [hy, hb]
    by_cases hs : ∃ (v : Fin 2 → Semiterm LAd ξ (_ + 1)) (B : Semiformula LAd ξ (_ + 1)),
      ψ = Semiformula.and (Semiformula.rel AdRel.mem v) B ∧
        (isBv0 (v 0) && !isBv0 (v 1)) = true
    · obtain ⟨v, B, rfl, hc⟩ := hs
      rw [relAt_exs_restr u v B hc, eval_exs', evalG_exs]
      have hc' := Bool.and_eq_true_iff.mp hc
      have h0 : v 0 = #0 := isBv0_eq hc'.1
      obtain ⟨t', ht'⟩ := isBv0_false_exists (t := v 1) (by simpa using hc'.2)
      have hct : Q (Semiterm.val (s := adStruc r P) b f t') := by
        cases t' with
        | bvar i => exact hb i
        | fvar i => exact hf i
        | func F _ => exact Empty.elim F
      have e0 : ∀ y, Semiterm.val (s := adStruc r P) (y :> b) f (v 0) = y := fun y => by
        simp [h0]
      have e1 : ∀ y, Semiterm.val (s := adStruc r P) (y :> b) f (v 1) =
          Semiterm.val (s := adStruc r P) b f t' := fun y => by simp [ht']
      have hR : ∀ y, Semiformula.Eval (s := adStruc r P) (y :> b) f
          (Semiformula.rel AdRel.mem v) ↔ r y (Semiterm.val (s := adStruc r P) b f t') :=
        fun y => by rw [eval_relmem, e0, e1]
      have hRG : ∀ y, EvalG r P D (y :> b) f (Semiformula.rel AdRel.mem v) ↔
          r y (Semiterm.val (s := adStruc r P) b f t') :=
        fun y => by rw [evalG_relmem, e0, e1]
      have key : ∀ y, r y (Semiterm.val (s := adStruc r P) b f t') →
          (Semiformula.Eval (s := adStruc r P) (y :> b) f (relAt (Rew.bShift u) B) ↔
            EvalG r P D (y :> b) f B) := by
        intro y hry
        have hDy := hT _ hct y hry
        have this : (Semiformula.Eval (s := adStruc r P) (y :> b) f (Semiformula.rel AdRel.mem v) ∧
            Semiformula.Eval (s := adStruc r P) (y :> b) f (relAt (Rew.bShift u) B)) ↔
            (EvalG r P D (y :> b) f (Semiformula.rel AdRel.mem v) ∧
              EvalG r P D (y :> b) f B) :=
          ih (Rew.bShift u) (y :> b) f (hb' y (hQD y hDy)) hf (hu' y)
        rw [hR, hRG] at this
        constructor
        · intro h; exact (this.mp ⟨hry, h⟩).2
        · intro h; exact (this.mpr ⟨hry, h⟩).2
      refine exists_congr fun y => ?_
      rw [eval_and', hR, evalG_and_relmem, e0, e1]
      constructor
      · rintro ⟨hry, h⟩
        exact ⟨hT _ hct y hry, hry, (key y hry).mp h⟩
      · rintro ⟨_, hry, h⟩
        exact ⟨hry, (key y hry).mpr h⟩
    · rw [relAt_exs_gen u ψ hs, eval_exs', evalG_exs]
      refine exists_congr fun y => ?_
      rw [eval_and', eval_memAt, val_bvar_zero, hu' y]
      constructor
      · rintro ⟨hry, h⟩
        have hDy := (hDx y).mp hry
        have := ih (Rew.bShift u) (y :> b) f (hb' y (hQD y hDy)) hf (hu' y)
        exact ⟨hDy, this.mp h⟩
      · rintro ⟨hDy, h⟩
        have := ih (Rew.bShift u) (y :> b) f (hb' y (hQD y hDy)) hf (hu' y)
        exact ⟨(hDx y).mpr hDy, this.mpr h⟩

end RelAtEval

/-! ### Substructures on a guard -/

section Sub

/-- the substructure on a guard -/
abbrev subRel (D : M → Prop) (a b : {a // D a}) : Prop := r a.1 b.1
abbrev subAd (D : M → Prop) (a : {a // D a}) : Prop := P a.1

theorem coe_cons {D : M → Prop} {n : ℕ} (x : {a // D a}) (b : Fin n → {a // D a}) :
    (fun i => ((x :> b) i).1) = (x.1 :> fun i => (b i).1) := by
  funext i
  cases i using Fin.cases <;> simp

theorem val_sub (D : M → Prop) {ξ : Type*} {n : ℕ} (b : Fin n → {a // D a})
    (f : ξ → {a // D a}) (t : Semiterm LAd ξ n) :
    (Semiterm.val (s := adStruc (subRel r D) (subAd P D)) b f t).1 =
      Semiterm.val (s := adStruc r P) (fun i => (b i).1) (fun j => (f j).1) t := by
  cases t with
  | bvar i => rfl
  | fvar j => rfl
  | func F _ => exact Empty.elim F

theorem rel_sub (D : M → Prop) {ξ : Type*} {n k : ℕ} (b : Fin n → {a // D a})
    (f : ξ → {a // D a}) (R : AdRel k) (v : Fin k → Semiterm LAd ξ n) :
    (adStruc (subRel r D) (subAd P D)).rel R
        (fun i => Semiterm.val (s := adStruc (subRel r D) (subAd P D)) b f (v i)) ↔
      (adStruc r P).rel R
        (fun i => Semiterm.val (s := adStruc r P) (fun i => (b i).1) (fun j => (f j).1) (v i)) := by
  cases R with
  | mem =>
    change r (Semiterm.val (s := adStruc (subRel r D) (subAd P D)) b f (v 0)).1
        (Semiterm.val (s := adStruc (subRel r D) (subAd P D)) b f (v 1)).1 ↔
      r (Semiterm.val (s := adStruc r P) (fun i => (b i).1) (fun j => (f j).1) (v 0))
        (Semiterm.val (s := adStruc r P) (fun i => (b i).1) (fun j => (f j).1) (v 1))
    rw [val_sub, val_sub]
  | ad =>
    change P (Semiterm.val (s := adStruc (subRel r D) (subAd P D)) b f (v 0)).1 ↔
      P (Semiterm.val (s := adStruc r P) (fun i => (b i).1) (fun j => (f j).1) (v 0))
    rw [val_sub]

/-- Δ₀ absoluteness for a downward-closed guard -/
theorem eval_sub_delta0 {D : M → Prop} (hD : ∀ c, D c → ∀ y, r y c → D y) {ξ : Type*} {n : ℕ}
    {φ : Semiformula LAd ξ n} (hφ : IsDelta0 φ) (b : Fin n → {a // D a}) (f : ξ → {a // D a}) :
    Semiformula.Eval (s := adStruc (subRel r D) (subAd P D)) b f φ ↔
      Semiformula.Eval (s := adStruc r P) (fun i => (b i).1) (fun j => (f j).1) φ := by
  induction hφ with
  | verum => exact Iff.rfl
  | falsum => exact Iff.rfl
  | mem s t => exact rel_sub r P D b f AdRel.mem ![s, t]
  | nmem s t => exact not_congr (rel_sub r P D b f AdRel.mem ![s, t])
  | ad t => exact rel_sub r P D b f AdRel.ad ![t]
  | nad t => exact not_congr (rel_sub r P D b f AdRel.ad ![t])
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ b) (ih₂ b)
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ b) (ih₂ b)
  | ball t _ ih =>
    rename_i φ'
    have hDt : D (Semiterm.val (s := adStruc r P) (fun i => (b i).1) (fun j => (f j).1) t) := by
      rw [← val_sub r P D b f t]
      exact (Semiterm.val (s := adStruc (subRel r D) (subAd P D)) b f t).2
    rw [eval_ballAt, eval_ballAt]
    constructor
    · intro h y hy
      have hDy := hD _ hDt y hy
      have h1 := h ⟨y, hDy⟩ (by
        change r y (Semiterm.val (s := adStruc (subRel r D) (subAd P D)) b f t).1
        rw [val_sub]; exact hy)
      have h2 := (ih (⟨y, hDy⟩ :> b)).mp h1
      rw [coe_cons] at h2
      exact h2
    · intro h x hx
      have hx' : r x.1 (Semiterm.val (s := adStruc r P) (fun i => (b i).1) (fun j => (f j).1) t) := by
        have hx2 : r x.1 (Semiterm.val (s := adStruc (subRel r D) (subAd P D)) b f t).1 := hx
        rwa [val_sub] at hx2
      refine (ih (x :> b)).mpr ?_
      rw [coe_cons]
      exact h x.1 hx'
  | bex t _ ih =>
    rename_i φ'
    have hDt : D (Semiterm.val (s := adStruc r P) (fun i => (b i).1) (fun j => (f j).1) t) := by
      rw [← val_sub r P D b f t]
      exact (Semiterm.val (s := adStruc (subRel r D) (subAd P D)) b f t).2
    rw [eval_bexAt, eval_bexAt]
    constructor
    · rintro ⟨x, hx, h⟩
      have hx2 : r x.1 (Semiterm.val (s := adStruc (subRel r D) (subAd P D)) b f t).1 := hx
      rw [val_sub] at hx2
      have h2 := (ih (x :> b)).mp h
      rw [coe_cons] at h2
      exact ⟨x.1, hx2, h2⟩
    · rintro ⟨y, hy, h⟩
      have hDy := hD _ hDt y hy
      refine ⟨⟨y, hDy⟩, ?_, ?_⟩
      · change r y (Semiterm.val (s := adStruc (subRel r D) (subAd P D)) b f t).1
        rw [val_sub]; exact hy
      · refine (ih (⟨y, hDy⟩ :> b)).mpr ?_
        rw [coe_cons]
        exact h

/-- guarded evaluation = evaluation in the substructure (any formula) -/
theorem evalG_iff_evalSub (D : M → Prop) {ξ : Type*} {n : ℕ} (φ : Semiformula LAd ξ n)
    (b : Fin n → {a // D a}) (f : ξ → {a // D a}) :
    EvalG r P D (fun i => (b i).1) (fun j => (f j).1) φ ↔
      Semiformula.Eval (s := adStruc (subRel r D) (subAd P D)) b f φ := by
  induction φ with
  | verum => exact Iff.rfl
  | falsum => exact Iff.rfl
  | rel R v => exact (rel_sub r P D b f R v).symm
  | nrel R v => exact not_congr (rel_sub r P D b f R v).symm
  | and _ _ ih₁ ih₂ => exact and_congr (ih₁ b) (ih₂ b)
  | or _ _ ih₁ ih₂ => exact or_congr (ih₁ b) (ih₂ b)
  | all ψ ih =>
    refine Iff.trans (evalG_all r P D (fun i => (b i).1) (fun j => (f j).1) ψ)
      (Iff.trans ?_ (eval_all' (subRel r D) (subAd P D) b f ψ).symm)
    constructor
    · intro h x
      refine (ih (x :> b)).mp ?_
      rw [coe_cons]
      exact h x.1 x.2
    · intro h y hy
      have h2 := (ih (⟨y, hy⟩ :> b)).mpr (h ⟨y, hy⟩)
      rw [coe_cons] at h2
      exact h2
  | exs ψ ih =>
    refine Iff.trans (evalG_exs r P D (fun i => (b i).1) (fun j => (f j).1) ψ)
      (Iff.trans ?_ (eval_exs' (subRel r D) (subAd P D) b f ψ).symm)
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨⟨y, hy⟩, (ih (⟨y, hy⟩ :> b)).mp ?_⟩
      rw [coe_cons]
      exact h
    · rintro ⟨x, h⟩
      have h2 := (ih (x :> b)).mpr h
      rw [coe_cons] at h2
      exact ⟨x.1, x.2, h2⟩

end Sub

/-- (Ad.3) unfolds to truth of the instance in the substructure below each admissible `x` -/
theorem holds_ad3_iff (hTr : ∀ x, P x → ∀ c, r c x → ∀ y, r y c → r y x) (ψ : Sentence LAd) :
    Holds r P (ad3Ax ψ) ↔ ∀ x, P x →
      Holds (subRel r (fun a => r a x)) (subAd P (fun a => r a x)) ψ := by
  show Semiformula.Eval (s := adStruc r P) ![] Empty.elim
      (∀¹ (adAt #0 🡒 relAt #0 (Rew.bShift ▹ ψ))) ↔ _
  rw [eval_all']
  refine forall_congr' fun x => ?_
  rw [eval_imp_adAt, val_bvar_zero]
  refine imp_congr_right fun hPx => ?_
  have hT : ∀ c, (r c x ∨ c = x) → ∀ y, r y c → r y x := by
    intro c hc y hy
    rcases hc with hc | rfl
    · exact hTr x hPx c hc y hy
    · exact hy
  have hb : ∀ i, (fun c => r c x ∨ c = x) ((x :> (![] : Fin 0 → M)) i) := by
    intro i
    have : i = 0 := Subsingleton.elim i 0
    subst this
    exact Or.inr rfl
  have hf : ∀ i : Empty, (fun c => r c x ∨ c = x) ((Empty.elim : Empty → M) i) :=
    fun i => Empty.elim i
  have hrel := eval_relAt_iff r P (fun a => r a x) (fun c => r c x ∨ c = x) x (fun _ => Iff.rfl)
    (fun _ => Or.inl) hT (Rew.bShift ▹ ψ) #0 (x :> ![]) Empty.elim hb hf
    (val_bvar_zero r P _ x ![])
  rw [hrel, evalG_bShift]
  have e1 : (fun i : Fin 0 => ((![] : Fin 0 → {a // r a x}) i).1) = (![] : Fin 0 → M) :=
    funext fun i => i.elim0
  have e2 : (fun j : Empty => ((Empty.elim j : {a // r a x})).1) = (Empty.elim : Empty → M) :=
    funext fun j => j.elim
  have h3 := evalG_iff_evalSub r P (fun a => r a x) ψ (![] : Fin 0 → {a // r a x})
    (Empty.elim : Empty → {a // r a x})
  rw [e1, e2] at h3
  exact h3

end OrdinalAnalysis.KPi.Sound
