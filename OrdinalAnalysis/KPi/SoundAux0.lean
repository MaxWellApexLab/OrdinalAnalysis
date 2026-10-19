module

public import OrdinalAnalysis.KPi.SlotCheck

@[expose] public section

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.Sound

open LO LO.FirstOrder

section Abstract

variable {M : Type*} (r : M → M → Prop) (P : M → Prop)

/-- The defined equality `x = y :≡ x ⊆ y ∧ y ⊆ x` of a structure `(M, r, P)` (B92). -/
def Eqm (x y : M) : Prop := (∀ a, r a x → r a y) ∧ (∀ a, r a y → r a x)

/-- the content of (Ext): `=` is a congruence for `∈` (left) and `Ad`. -/
def ExtOK : Prop := ∀ x y z, Eqm r x y → (r x z → r y z) ∧ (P x → P y)

variable {r P}

theorem Eqm.refl (x : M) : Eqm r x x := ⟨fun _ h => h, fun _ h => h⟩

theorem Eqm.symm {x y : M} (h : Eqm r x y) : Eqm r y x := ⟨h.2, h.1⟩

theorem Eqm.trans {x y z : M} (h1 : Eqm r x y) (h2 : Eqm r y z) : Eqm r x z :=
  ⟨fun a ha => h2.1 a (h1.1 a ha), fun a ha => h1.2 a (h2.2 a ha)⟩

theorem ExtOK.mem_left (h : ExtOK r P) {x y z : M} (e : Eqm r x y) : r x z ↔ r y z :=
  ⟨(h x y z e).1, (h y x z e.symm).1⟩

theorem ExtOK.mem_right {x y z : M} (e : Eqm r y z) : r x y ↔ r x z :=
  ⟨e.1 x, e.2 x⟩

theorem ExtOK.ad (h : ExtOK r P) {x y : M} (e : Eqm r x y) : P x ↔ P y :=
  ⟨(h x y x e).2, (h y x x e.symm).2⟩

@[simp] theorem eval_nadAt {ξ : Type*} {n : ℕ} (b : Fin n → M) (f : ξ → M) (t : Semiterm LAd ξ n) :
    Semiformula.Eval (s := adStruc r P) b f (nadAt t) ↔
      ¬ P (Semiterm.val (s := adStruc r P) b f t) :=
  Iff.rfl

theorem val_eqm {ξ : Type*} {n : ℕ} (b b' : Fin n → M) (f f' : ξ → M)
    (hb : ∀ i, Eqm r (b i) (b' i)) (hf : ∀ j, Eqm r (f j) (f' j)) (t : Semiterm LAd ξ n) :
    Eqm r (Semiterm.val (s := adStruc r P) b f t) (Semiterm.val (s := adStruc r P) b' f' t) := by
  cases t with
  | bvar i => exact hb i
  | fvar j => exact hf j
  | func g _ => exact Empty.elim g

theorem cons_eqm {n : ℕ} (x : M) {b b' : Fin n → M} (hb : ∀ i, Eqm r (b i) (b' i)) :
    ∀ i, Eqm r ((x :> b) i) ((x :> b') i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Eqm.refl x
  · simpa using hb j

/-- Δ₀-formulas are congruent for the defined equality (from (Ext) only). -/
theorem eval_congr_delta0 (hext : ExtOK r P) :
    ∀ {n : ℕ} {φ : Semiformula LAd ℕ n}, IsDelta0 φ →
    ∀ (b b' : Fin n → M) (f f' : ℕ → M), (∀ i, Eqm r (b i) (b' i)) → (∀ j, Eqm r (f j) (f' j)) →
      (Semiformula.Eval (s := adStruc r P) b f φ ↔ Semiformula.Eval (s := adStruc r P) b' f' φ) := by
  intro n φ hφ
  induction hφ with
  | verum => intros; simp
  | falsum => intros; simp
  | mem s t =>
    intro b b' f f' hb hf
    simp only [eval_memAt]
    rw [hext.mem_left (val_eqm b b' f f' hb hf s), ExtOK.mem_right (val_eqm b b' f f' hb hf t)]
  | nmem s t =>
    intro b b' f f' hb hf
    simp only [eval_nmemAt]
    rw [hext.mem_left (val_eqm b b' f f' hb hf s), ExtOK.mem_right (val_eqm b b' f f' hb hf t)]
  | ad t =>
    intro b b' f f' hb hf
    simp only [eval_adAt]
    rw [hext.ad (val_eqm b b' f f' hb hf t)]
  | nad t =>
    intro b b' f f' hb hf
    simp only [eval_nadAt]
    rw [hext.ad (val_eqm b b' f f' hb hf t)]
  | and _ _ ih₁ ih₂ =>
    intro b b' f f' hb hf
    simp [ih₁ b b' f f' hb hf, ih₂ b b' f f' hb hf]
  | or _ _ ih₁ ih₂ =>
    intro b b' f f' hb hf
    simp [ih₁ b b' f f' hb hf, ih₂ b b' f f' hb hf]
  | ball t _ ih =>
    intro b b' f f' hb hf
    simp only [eval_ballAt]
    have e := val_eqm (P := P) b b' f f' hb hf t
    refine forall_congr' fun x => ?_
    rw [ExtOK.mem_right e]
    exact imp_congr_right fun _ => ih (x :> b) (x :> b') f f' (cons_eqm x hb) hf
  | bex t _ ih =>
    intro b b' f f' hb hf
    simp only [eval_bexAt]
    have e := val_eqm (P := P) b b' f f' hb hf t
    refine exists_congr fun x => ?_
    rw [ExtOK.mem_right e]
    exact and_congr_right fun _ => ih (x :> b) (x :> b') f f' (cons_eqm x hb) hf

end Abstract

end OrdinalAnalysis.KPi.Sound
