/-
  The old notation sits inside the new one.

  `ofWT : ThetaWTerm → ThetaVTerm` is the identity on the constructors (`Ω_ω`-free terms).  It
  preserves and reflects the order, the normal form and the domain condition, and commutes with
  `E_k` and `G_k`.  So `ofW : ThetaWNoteD ↪o ThetaVNoteD` is an order embedding, and its countable
  part lies below `ϑ₀(Ω_ω)`: the countable part of the old notation (intended order type
  `ψ₀(Ω_ω)`) is a proper initial segment of the countable part of the new one.
-/
import OrdinalAnalysis.Ordinal.ThetaW.Dom
import OrdinalAnalysis.Ordinal.ThetaV.Dom
import Mathlib.Order.Hom.Basic

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaVTerm

mutual
/-- The old terms as new terms. -/
def ofWT : ThetaWTerm → ThetaVTerm
  | .Omega k => Omega k
  | .theta k a => theta k (ofWT a)
  | .sum xs => sum (ofWList xs)
/-- `ofWT` on lists. -/
def ofWList : List ThetaWTerm → List ThetaVTerm
  | [] => []
  | x :: xs => ofWT x :: ofWList xs
end

mutual
/-- A left inverse of `ofWT` (sending `Ω_ω` to an arbitrary old term). -/
def toWT : ThetaVTerm → ThetaWTerm
  | Omega k => .Omega k
  | OmegaW => .Omega 0
  | theta k a => .theta k (toWT a)
  | sum xs => .sum (toWList xs)
/-- `toWT` on lists. -/
def toWList : List ThetaVTerm → List ThetaWTerm
  | [] => []
  | x :: xs => toWT x :: toWList xs
end

theorem ofWList_eq_map (xs : List ThetaWTerm) : ofWList xs = xs.map ofWT := by
  induction xs with
  | nil => simp [ofWList]
  | cons x xs ih => simp [ofWList, ih]

@[simp] theorem ofWT_Omega (k : ℕ) : ofWT (.Omega k) = Omega k := by simp [ofWT]

@[simp] theorem ofWT_theta (k : ℕ) (a : ThetaWTerm) : ofWT (.theta k a) = theta k (ofWT a) := by
  simp [ofWT]

@[simp] theorem ofWT_sum (xs : List ThetaWTerm) : ofWT (.sum xs) = sum (xs.map ofWT) := by
  simp [ofWT, ofWList_eq_map]

theorem toWT_ofWT : ∀ a : ThetaWTerm, toWT (ofWT a) = a
  | .Omega k => by simp [toWT]
  | .theta k a => by simp [toWT, toWT_ofWT a]
  | .sum xs => by
    have hl : ∀ ys : List ThetaWTerm, (∀ y ∈ ys, toWT (ofWT y) = y) →
        toWList (ys.map ofWT) = ys := by
      intro ys h
      induction ys with
      | nil => simp [toWList]
      | cons y ys ih =>
        simp only [List.map_cons, toWList]
        rw [h y List.mem_cons_self, ih (fun z hz => h z (List.mem_cons_of_mem y hz))]
    rw [ofWT_sum]
    simp only [toWT]
    rw [hl xs (fun y hy => toWT_ofWT y)]
termination_by a => ThetaWTerm.l a
decreasing_by
  · simp
  · exact ThetaWTerm.l_lt_of_mem hy

theorem ofWT_injective : Function.Injective ofWT :=
  Function.LeftInverse.injective toWT_ofWT

@[simp] theorem l_ofWT : ∀ a : ThetaWTerm, l (ofWT a) = ThetaWTerm.l a
  | .Omega k => by simp
  | .theta k a => by simp [l_ofWT a]
  | .sum [] => by simp
  | .sum (x :: xs) => by
    have h1 := l_ofWT x
    have h2 := l_ofWT (.sum xs)
    simp only [ofWT_sum] at h2
    simp [h1, h2]
termination_by a => ThetaWTerm.l a
decreasing_by all_goals simp; try omega

theorem E_ofWT (k : ℕ) : ∀ a : ThetaWTerm, E k (ofWT a) = (ThetaWTerm.E k a).map ofWT
  | .Omega j => by simp
  | .theta j a => by
    by_cases hj : j ≤ k
    · rw [ofWT_theta, E_theta_of_le hj, ThetaWTerm.E_theta_of_le hj]; simp
    · rw [ofWT_theta, E_theta_of_lt (Nat.lt_of_not_le hj),
        ThetaWTerm.E_theta_of_lt (Nat.lt_of_not_le hj), E_ofWT k a]
  | .sum [] => by simp
  | .sum (x :: xs) => by
    have h1 := E_ofWT k x
    have h2 := E_ofWT k (.sum xs)
    rw [ofWT_sum] at h2
    rw [ofWT_sum, List.map_cons, E_cons, ThetaWTerm.E_cons, List.map_append, h1, h2]
termination_by a => ThetaWTerm.l a
decreasing_by all_goals simp; try omega

theorem G_ofWT (k : ℕ) : ∀ a : ThetaWTerm, G k (ofWT a) = (ThetaWTerm.G k a).map ofWT
  | .Omega j => by simp
  | .theta j a => by
    by_cases hj : k < j
    · rw [ofWT_theta, G_theta_of_lt hj, ThetaWTerm.G_theta_of_lt hj, G_ofWT k a]; simp
    · rw [ofWT_theta, G_theta_of_le (Nat.le_of_not_lt hj),
        ThetaWTerm.G_theta_of_le (Nat.le_of_not_lt hj)]; simp
  | .sum [] => by simp
  | .sum (x :: xs) => by
    have h1 := G_ofWT k x
    have h2 := G_ofWT k (.sum xs)
    rw [ofWT_sum] at h2
    rw [ofWT_sum, List.map_cons, G_cons, ThetaWTerm.G_cons, List.map_append, h1, h2]
termination_by a => ThetaWTerm.l a
decreasing_by all_goals simp; try omega

/-! ### The order -/

theorem ofWT_lt_iff_aux (n : ℕ) : ∀ a b : ThetaWTerm, ThetaWTerm.l a + ThetaWTerm.l b ≤ n →
    (ofWT a < ofWT b ↔ a < b) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn
  have IH : ∀ x y : ThetaWTerm, ThetaWTerm.l x + ThetaWTerm.l y < ThetaWTerm.l a + ThetaWTerm.l b →
      (ofWT x < ofWT y ↔ x < y) := fun x y h => ih _ (by omega) x y le_rfl
  have IHle : ∀ x y : ThetaWTerm,
      ThetaWTerm.l x + ThetaWTerm.l y < ThetaWTerm.l a + ThetaWTerm.l b →
      (ofWT x ≤ ofWT y ↔ x ≤ y) := fun x y h => by
    rw [le_def, ThetaWTerm.le_def, IH x y h, ofWT_injective.eq_iff]
  cases a with
  | Omega i =>
    cases b with
    | Omega j => rw [ofWT_Omega, ofWT_Omega, Omega_lt_Omega_iff, ThetaWTerm.Omega_lt_Omega_iff]
    | theta j b => rw [ofWT_Omega, ofWT_theta, Omega_lt_theta_iff, ThetaWTerm.Omega_lt_theta_iff]
    | sum ys =>
      cases ys with
      | nil =>
        rw [ofWT_Omega, ofWT_sum, List.map_nil]
        exact iff_of_false (not_Omega_lt_nil i) (ThetaWTerm.not_Omega_lt_nil i)
      | cons y ys =>
        rw [ofWT_Omega, ofWT_sum, List.map_cons, Omega_lt_cons_iff, ThetaWTerm.Omega_lt_cons_iff]
        have := IHle (.Omega i) y (by simp; omega)
        rwa [ofWT_Omega] at this
  | theta i a =>
    cases b with
    | Omega j => rw [ofWT_Omega, ofWT_theta, theta_lt_Omega_iff, ThetaWTerm.theta_lt_Omega_iff]
    | theta j b =>
      rw [ofWT_theta, ofWT_theta]
      rcases Nat.lt_trichotomy i j with h | rfl | h
      · exact iff_of_true (theta_lt_theta_of_lt_level _ _ h)
          (ThetaWTerm.theta_lt_theta_of_lt_level _ _ h)
      · have IHab := IH a b (by simp; omega)
        have IHE1 : ∀ g ∈ ThetaWTerm.E i a,
            (ofWT g < theta i (ofWT b) ↔ g < ThetaWTerm.theta i b) := fun g hg => by
          have := ThetaWTerm.l_le_of_mem_E hg
          have h' := IH g (.theta i b) (by simp; omega)
          rwa [ofWT_theta] at h'
        have IHE2 : ∀ g ∈ ThetaWTerm.E i b,
            (theta i (ofWT a) ≤ ofWT g ↔ ThetaWTerm.theta i a ≤ g) := fun g hg => by
          have := ThetaWTerm.l_le_of_mem_E hg
          have h' := IHle (.theta i a) g (by simp; omega)
          rwa [ofWT_theta] at h'
        rw [theta_lt_theta_iff, ThetaWTerm.theta_lt_theta_iff, E_ofWT, E_ofWT, IHab]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨g', hg', h3⟩)
          · exact Or.inl ⟨h1, fun g hg => (IHE1 g hg).mp (h2 _ (List.mem_map_of_mem hg))⟩
          · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
            exact Or.inr ⟨g, hg, (IHE2 g hg).mp h3⟩
        · rintro (⟨h1, h2⟩ | ⟨g, hg, h3⟩)
          · refine Or.inl ⟨h1, fun g' hg' => ?_⟩
            obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
            exact (IHE1 g hg).mpr (h2 g hg)
          · exact Or.inr ⟨ofWT g, List.mem_map_of_mem hg, (IHE2 g hg).mpr h3⟩
      · exact iff_of_false (not_theta_lt_theta_of_lt_level _ _ h)
          (ThetaWTerm.not_theta_lt_theta_of_lt_level _ _ h)
    | sum ys =>
      cases ys with
      | nil =>
        rw [ofWT_theta, ofWT_sum, List.map_nil]
        exact iff_of_false (not_theta_lt_nil i _) (ThetaWTerm.not_theta_lt_nil i a)
      | cons y ys =>
        rw [ofWT_theta, ofWT_sum, List.map_cons, theta_lt_cons_iff, ThetaWTerm.theta_lt_cons_iff]
        have := IHle (.theta i a) y (by simp; omega)
        rwa [ofWT_theta] at this
  | sum xs =>
    cases xs with
    | nil =>
      cases b with
      | Omega j =>
        rw [ofWT_sum, List.map_nil, ofWT_Omega]
        exact iff_of_true (nil_lt_Omega j) (ThetaWTerm.nil_lt_Omega j)
      | theta j b =>
        rw [ofWT_sum, List.map_nil, ofWT_theta]
        exact iff_of_true (nil_lt_theta j _) (ThetaWTerm.nil_lt_theta j b)
      | sum ys =>
        cases ys with
        | nil =>
          rw [ofWT_sum, List.map_nil]
          exact iff_of_false not_nil_lt_nil ThetaWTerm.not_nil_lt_nil
        | cons y ys =>
          rw [ofWT_sum, ofWT_sum, List.map_nil, List.map_cons]
          exact iff_of_true (nil_lt_cons _ _) (ThetaWTerm.nil_lt_cons y ys)
    | cons x xs =>
      cases b with
      | Omega j =>
        rw [ofWT_sum, List.map_cons, ofWT_Omega, cons_lt_Omega_iff, ThetaWTerm.cons_lt_Omega_iff]
        have := IH x (.Omega j) (by simp; omega)
        rwa [ofWT_Omega] at this
      | theta j b =>
        rw [ofWT_sum, List.map_cons, ofWT_theta, cons_lt_theta_iff, ThetaWTerm.cons_lt_theta_iff]
        have := IH x (.theta j b) (by simp; omega)
        rwa [ofWT_theta] at this
      | sum ys =>
        cases ys with
        | nil =>
          rw [ofWT_sum, ofWT_sum, List.map_nil, List.map_cons]
          exact iff_of_false (not_cons_lt_nil _ _) (ThetaWTerm.not_cons_lt_nil x xs)
        | cons y ys =>
          rw [ofWT_sum, ofWT_sum, List.map_cons, List.map_cons, cons_lt_cons_iff,
            ThetaWTerm.cons_lt_cons_iff, IH x y (by simp; omega), ofWT_injective.eq_iff]
          have h' := IH (.sum xs) (.sum ys) (by simp; omega)
          rw [ofWT_sum, ofWT_sum] at h'
          rw [h']

/-- `ofWT` preserves and reflects the order. -/
theorem ofWT_lt_iff {a b : ThetaWTerm} : ofWT a < ofWT b ↔ a < b :=
  ofWT_lt_iff_aux _ a b le_rfl

theorem ofWT_le_iff {a b : ThetaWTerm} : ofWT a ≤ ofWT b ↔ a ≤ b := by
  rw [le_def, ThetaWTerm.le_def, ofWT_lt_iff, ofWT_injective.eq_iff]

/-! ### Normal form, domain, `Ω_ω`-freeness -/

theorem desc_map_ofWT : ∀ xs : List ThetaWTerm, Desc (xs.map ofWT) ↔ ThetaWTerm.Desc xs
  | [] => by simp
  | [_] => by simp
  | x :: y :: ys => by
    rw [List.map_cons, List.map_cons, desc_cons_cons, ThetaWTerm.desc_cons_cons, ofWT_le_iff,
      ← List.map_cons, desc_map_ofWT (y :: ys)]

theorem singleOK_map_ofWT : ∀ xs : List ThetaWTerm, SingleOK (xs.map ofWT) ↔ ThetaWTerm.SingleOK xs
  | [] => by simp [SingleOK, ThetaWTerm.SingleOK]
  | [x] => by
    cases x <;> simp [SingleOK, ThetaWTerm.SingleOK, IsPrin, ThetaWTerm.IsPrin]
  | _ :: _ :: _ => by simp [SingleOK, ThetaWTerm.SingleOK]

theorem nf_ofWT : ∀ a : ThetaWTerm, NF (ofWT a) ↔ ThetaWTerm.NF a
  | .Omega k => by simp
  | .theta k a => by rw [ofWT_theta, nf_theta_iff, ThetaWTerm.nf_theta_iff, nf_ofWT a]
  | .sum xs => by
    rw [ofWT_sum, nf_sum_iff, ThetaWTerm.nf_sum_iff, desc_map_ofWT, singleOK_map_ofWT]
    have h1 : (∀ x ∈ xs.map ofWT, NF x) ↔ ∀ x ∈ xs, ThetaWTerm.NF x := by
      constructor
      · intro h x hx; exact (nf_ofWT x).mp (h _ (List.mem_map_of_mem hx))
      · intro h x' hx'
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hx'
        exact (nf_ofWT x).mpr (h x hx)
    rw [h1]
termination_by a => ThetaWTerm.l a
decreasing_by
  · simp
  · exact ThetaWTerm.l_lt_of_mem hx
  · exact ThetaWTerm.l_lt_of_mem hx

theorem dom_ofWT : ∀ a : ThetaWTerm, Dom (ofWT a) ↔ ThetaWTerm.Dom a
  | .Omega k => by simp
  | .theta k a => by
    rw [ofWT_theta, dom_theta_iff, ThetaWTerm.dom_theta_iff, dom_ofWT a, G_ofWT]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => ofWT_lt_iff.mp (h2 _ (List.mem_map_of_mem hx))⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun x' hx' => ?_⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hx'
      exact ofWT_lt_iff.mpr (h2 x hx)
  | .sum xs => by
    rw [ofWT_sum, dom_sum_iff, ThetaWTerm.dom_sum_iff]
    constructor
    · intro h x hx; exact (dom_ofWT x).mp (h _ (List.mem_map_of_mem hx))
    · intro h x' hx'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hx'
      exact (dom_ofWT x).mpr (h x hx)
termination_by a => ThetaWTerm.l a
decreasing_by
  · simp
  · exact ThetaWTerm.l_lt_of_mem hx
  · exact ThetaWTerm.l_lt_of_mem hx

theorem wFree_ofWT : ∀ a : ThetaWTerm, WFree (ofWT a)
  | .Omega k => by simp
  | .theta k a => by rw [ofWT_theta, wFree_theta_iff]; exact wFree_ofWT a
  | .sum xs => by
    rw [ofWT_sum, wFree_sum_iff]
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hx'
    exact wFree_ofWT x
termination_by a => ThetaWTerm.l a
decreasing_by
  · simp
  · exact ThetaWTerm.l_lt_of_mem hx

end ThetaVTerm

namespace ThetaVNoteD

/-- The old notation as new notations. -/
def ofWFun (a : ThetaWNoteD) : ThetaVNoteD :=
  ⟨ThetaVTerm.ofWT a.1, (ThetaVTerm.nf_ofWT _).mpr a.2.1, (ThetaVTerm.dom_ofWT _).mpr a.2.2⟩

/-- **The old notation sits inside the new one**: `ofW : ThetaWNoteD ↪o ThetaVNoteD`. -/
def ofW : ThetaWNoteD ↪o ThetaVNoteD :=
  OrderEmbedding.ofStrictMono ofWFun fun _ _ h => ThetaVTerm.ofWT_lt_iff.mpr h

theorem ofW_apply (a : ThetaWNoteD) : (ofW a).1 = ThetaVTerm.ofWT a.1 := rfl

/-- The countable part of the old notation lies below `ϑ₀(Ω_ω)`. -/
theorem ofW_lt_thetaOmegaW_zero (a : ThetaWNoteD) (h : a.1 < ThetaWTerm.Omega 0) :
    ofW a < thetaOmegaW 0 := by
  show ThetaVTerm.ofWT a.1 < ThetaVTerm.theta 0 ThetaVTerm.OmegaW
  refine ThetaVTerm.lt_theta0_OmegaW_of_wFree ((ThetaVTerm.nf_ofWT _).mpr a.2.1)
    (ThetaVTerm.wFree_ofWT _) ?_
  have := (ThetaVTerm.ofWT_lt_iff (a := a.1) (b := ThetaWTerm.Omega 0)).mpr h
  rwa [ThetaVTerm.ofWT_Omega] at this

end ThetaVNoteD

end OrdinalAnalysis
