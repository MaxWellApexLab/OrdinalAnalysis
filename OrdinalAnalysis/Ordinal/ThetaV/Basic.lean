/-
  The ϑ-notation with all finite levels and `Ω_ω`: terms, length, the level-`k` coefficient
  sets, the order, and the normal form.

  This is the system of `ThetaW/Basic` with one more constructor, `OmegaW`, denoting `Ω_ω`.

  Terms.  For every level `k : ℕ`:
  * `Omega k` denotes `Ω_{k+1}`;
  * `OmegaW` denotes `Ω_ω`, a principal term above every `Omega k` and every `theta k α`;
  * `theta k α` denotes `ϑ_k α`, in the interval `(Ω_k, Ω_{k+1})`; the argument is unrestricted,
    so `ϑ_k(Ω_ω)`, `ϑ_k(Ω_ω + 1)`, … are terms;
  * `sum [α₀, …, α_{n-1}]` denotes `ω^α₀ + ⋯ + ω^α_{n-1}`.

  `OmegaW` is a constant: it is not a collapse and has no arguments, so it contributes nothing to
  the coefficient sets: `E_k(Ω_ω) = ∅` (and `G_k(Ω_ω) = ∅`, `ThetaV/Dom`), as for `Ω_{j+1}`.

  The order (clauses as in `ThetaW/Basic`, plus): `P ≺ Ω_ω` for every principal `P ≠ Ω_ω`, and
  `Ω_ω ⊀ P` for every principal `P`; against sums `Ω_ω` behaves as any principal term (Freund,
  arXiv:2204.09321, Definition 3.1 (i')).

  Computation.  The order is specified by a well-founded recursion `ltbS` (on `l α + l β`, as in
  `ThetaW/Basic`), which the kernel does not unfold; the `<` instance is the same function
  computed with fuel, `ltbF (l α + l β + 1)`, a structural recursion, so that closed comparisons
  (and `NF`, `Dom`) are decided by `decide`.  `ltbF_eq` identifies the two.
-/
import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace OrdinalAnalysis

/-- Raw terms of the ϑ-notation with `Ω_ω`: `Omega k` is `Ω_{k+1}`, `OmegaW` is `Ω_ω`,
`theta k α` is `ϑ_k α`, and `sum [α₀, …, α_{n-1}]` is `⟨α₀, …, α_{n-1}⟩`. -/
inductive ThetaVTerm : Type
  | Omega : ℕ → ThetaVTerm
  | OmegaW : ThetaVTerm
  | theta : ℕ → ThetaVTerm → ThetaVTerm
  | sum : List ThetaVTerm → ThetaVTerm
  deriving Repr

namespace ThetaVTerm

/-! ### Decidable equality -/

mutual
/-- Decidable equality of terms, by structural recursion. -/
def decEq : (a b : ThetaVTerm) → Decidable (a = b)
  | Omega i, Omega j =>
    if h : i = j then isTrue (h ▸ rfl) else isFalse (fun e => h (Omega.inj e))
  | Omega _, OmegaW => isFalse (fun h => ThetaVTerm.noConfusion h)
  | Omega _, theta _ _ => isFalse (fun h => ThetaVTerm.noConfusion h)
  | Omega _, sum _ => isFalse (fun h => ThetaVTerm.noConfusion h)
  | OmegaW, Omega _ => isFalse (fun h => ThetaVTerm.noConfusion h)
  | OmegaW, OmegaW => isTrue rfl
  | OmegaW, theta _ _ => isFalse (fun h => ThetaVTerm.noConfusion h)
  | OmegaW, sum _ => isFalse (fun h => ThetaVTerm.noConfusion h)
  | theta _ _, Omega _ => isFalse (fun h => ThetaVTerm.noConfusion h)
  | theta _ _, OmegaW => isFalse (fun h => ThetaVTerm.noConfusion h)
  | theta i a, theta j b =>
    if h : i = j then
      match decEq a b with
      | isTrue h' => isTrue (h ▸ h' ▸ rfl)
      | isFalse h' => isFalse (fun e => h' (theta.inj e).2)
    else isFalse (fun e => h (theta.inj e).1)
  | theta _ _, sum _ => isFalse (fun h => ThetaVTerm.noConfusion h)
  | sum _, Omega _ => isFalse (fun h => ThetaVTerm.noConfusion h)
  | sum _, OmegaW => isFalse (fun h => ThetaVTerm.noConfusion h)
  | sum _, theta _ _ => isFalse (fun h => ThetaVTerm.noConfusion h)
  | sum xs, sum ys =>
    match decEqList xs ys with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => h (sum.inj e))
/-- Decidable equality of lists of terms, by structural recursion. -/
def decEqList : (xs ys : List ThetaVTerm) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | x :: xs, y :: ys =>
    match decEq x y, decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h1, _ => isFalse (fun e => h1 (List.cons.inj e).1)
    | _, isFalse h2 => isFalse (fun e => h2 (List.cons.inj e).2)
end

instance : DecidableEq ThetaVTerm := decEq

/-- The term `0 = ⟨⟩`. -/
def zero : ThetaVTerm := sum []

/-- `Ω_{k+1}`, `Ω_ω` and the terms `ϑ_k α` are the principal terms. -/
def IsPrin : ThetaVTerm → Prop
  | Omega _ => True
  | OmegaW => True
  | theta _ _ => True
  | sum _ => False

instance : DecidablePred IsPrin := fun a =>
  match a with
  | Omega _ => isTrue trivial
  | OmegaW => isTrue trivial
  | theta _ _ => isTrue trivial
  | sum _ => isFalse id

@[simp] theorem isPrin_Omega (k : ℕ) : IsPrin (Omega k) := trivial
@[simp] theorem isPrin_OmegaW : IsPrin OmegaW := trivial
@[simp] theorem isPrin_theta (k : ℕ) (a : ThetaVTerm) : IsPrin (theta k a) := trivial
@[simp] theorem not_isPrin_sum (xs : List ThetaVTerm) : ¬ IsPrin (sum xs) := id

/-- The principal terms other than `Ω_ω`: those of some finite level. -/
def IsPrinB : ThetaVTerm → Prop
  | Omega _ => True
  | OmegaW => False
  | theta _ _ => True
  | sum _ => False

theorem IsPrinB.isPrin {p : ThetaVTerm} (h : IsPrinB p) : IsPrin p := by
  cases p <;> simp_all [IsPrinB, IsPrin]

theorem isPrinB_or_eq_OmegaW {p : ThetaVTerm} (h : IsPrin p) : IsPrinB p ∨ p = OmegaW := by
  cases p <;> simp_all [IsPrinB, IsPrin]

theorem IsPrinB.ne_OmegaW {p : ThetaVTerm} (h : IsPrinB p) : p ≠ OmegaW := by
  rintro rfl; exact h

/-- The position of a principal term of finite level: `ϑ_k`-terms at `2k`, `Ω_{k+1}` at
`2k + 1`.  The value on `Ω_ω` and on sums is irrelevant. -/
def key : ThetaVTerm → ℕ
  | Omega k => 2 * k + 1
  | OmegaW => 0
  | theta k _ => 2 * k
  | sum _ => 0

@[simp] theorem key_Omega (k : ℕ) : key (Omega k) = 2 * k + 1 := rfl
@[simp] theorem key_theta (k : ℕ) (a : ThetaVTerm) : key (theta k a) = 2 * k := rfl

/-! ### Length -/

mutual
/-- The length function: `l(Ω_{k+1}) = l(Ω_ω) = 0`, `l(ϑ_k α) = l(α) + 1`,
`l(⟨α₀, …, α_{n-1}⟩) = n + Σ l(α_i)`. -/
def l : ThetaVTerm → ℕ
  | Omega _ => 0
  | OmegaW => 0
  | theta _ a => l a + 1
  | sum xs => lList xs
/-- `lList [α₀, …, α_{n-1}] = n + Σ l(α_i)`. -/
def lList : List ThetaVTerm → ℕ
  | [] => 0
  | x :: xs => l x + 1 + lList xs
end

@[simp] theorem l_Omega (k : ℕ) : l (Omega k) = 0 := by simp [l]
@[simp] theorem l_OmegaW : l OmegaW = 0 := by simp [l]
@[simp] theorem l_theta (k : ℕ) (a : ThetaVTerm) : l (theta k a) = l a + 1 := by simp [l]
@[simp] theorem l_nil : l (sum []) = 0 := by simp [l, lList]
@[simp] theorem l_cons (x : ThetaVTerm) (xs : List ThetaVTerm) :
    l (sum (x :: xs)) = l x + 1 + l (sum xs) := by simp [l, lList]

theorem l_lt_of_mem {x : ThetaVTerm} {xs : List ThetaVTerm} (h : x ∈ xs) :
    l x < l (sum xs) := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp; omega
    · have := ih h; simp; omega

/-! ### The level-`k` coefficient sets `E_k` -/

mutual
/-- The level-`k` coefficient set `E_k(α)`: `E_k(Ω_{j+1}) = E_k(Ω_ω) = ∅`,
`E_k(ϑ_j δ) = {ϑ_j δ}` for `j ≤ k`, `E_k(ϑ_j δ) = E_k(δ)` for `j > k`, and
`E_k(⟨α₀, …⟩) = ⋃ E_k(α_i)`. -/
def E (k : ℕ) : ThetaVTerm → List ThetaVTerm
  | Omega _ => []
  | OmegaW => []
  | theta j a => if j ≤ k then [theta j a] else E k a
  | sum xs => EList k xs
/-- The union of the `E_k(α_i)` over a list. -/
def EList (k : ℕ) : List ThetaVTerm → List ThetaVTerm
  | [] => []
  | x :: xs => E k x ++ EList k xs
end

@[simp] theorem E_Omega (k j : ℕ) : E k (Omega j) = [] := by simp [E]

@[simp] theorem E_OmegaW (k : ℕ) : E k OmegaW = [] := by simp [E]

theorem E_theta_of_le {k j : ℕ} (h : j ≤ k) (a : ThetaVTerm) :
    E k (theta j a) = [theta j a] := by simp [E, h]

theorem E_theta_of_lt {k j : ℕ} (h : k < j) (a : ThetaVTerm) :
    E k (theta j a) = E k a := by simp [E, Nat.not_le.mpr h]

@[simp] theorem E_nil (k : ℕ) : E k (sum []) = [] := by simp [E, EList]

@[simp] theorem E_cons (k : ℕ) (x : ThetaVTerm) (xs : List ThetaVTerm) :
    E k (sum (x :: xs)) = E k x ++ E k (sum xs) := by simp [E, EList]

theorem mem_E_sum {k : ℕ} {g : ThetaVTerm} {xs : List ThetaVTerm} :
    g ∈ E k (sum xs) ↔ ∃ x ∈ xs, g ∈ E k x := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp [ih]

theorem mem_E_of_mem {k : ℕ} {x g : ThetaVTerm} {xs : List ThetaVTerm} (hx : x ∈ xs)
    (hg : g ∈ E k x) : g ∈ E k (sum xs) :=
  mem_E_sum.mpr ⟨x, hx, hg⟩

/-- `δ ∈ E_k(α)` implies `l(δ) ≤ l(α)`. -/
theorem l_le_of_mem_E {k : ℕ} : ∀ {a g : ThetaVTerm}, g ∈ E k a → l g ≤ l a
  | Omega _, g, h => by simp at h
  | OmegaW, g, h => by simp at h
  | theta j a, g, h => by
    by_cases hj : j ≤ k
    · rw [E_theta_of_le hj] at h; simp at h; simp [h]
    · rw [E_theta_of_lt (Nat.lt_of_not_le hj)] at h
      have := l_le_of_mem_E h
      simp; omega
  | sum xs, g, h => by
    obtain ⟨x, hx, hg⟩ := mem_E_sum.mp h
    have := l_lt_of_mem hx
    have := l_le_of_mem_E hg
    omega
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hx

/-- Every element of `E_k(α)` is a term `ϑ_j δ` with `j ≤ k`. -/
theorem exists_eq_theta_of_mem_E {k : ℕ} :
    ∀ {a g : ThetaVTerm}, g ∈ E k a → ∃ j d, j ≤ k ∧ g = theta j d
  | Omega _, g, h => by simp at h
  | OmegaW, g, h => by simp at h
  | theta j a, g, h => by
    by_cases hj : j ≤ k
    · rw [E_theta_of_le hj] at h; simp at h; exact ⟨j, a, hj, h⟩
    · rw [E_theta_of_lt (Nat.lt_of_not_le hj)] at h
      exact exists_eq_theta_of_mem_E h
  | sum xs, g, h => by
    obtain ⟨x, hx, hg⟩ := mem_E_sum.mp h
    exact exists_eq_theta_of_mem_E hg
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hx

/-! ### The order, specified by well-founded recursion -/

/-- The ϑ-order with `Ω_ω`, as a boolean function (the specification; the `<` instance computes
it with fuel, `ltbF`). -/
def ltbS : ThetaVTerm → ThetaVTerm → Bool
  -- principal against principal
  | Omega i, Omega j => decide (i < j)
  | Omega _, OmegaW => true
  | Omega i, theta j _ => decide (i < j)
  | OmegaW, Omega _ => false
  | OmegaW, OmegaW => false
  | OmegaW, theta _ _ => false
  | theta i _, Omega j => decide (i ≤ j)
  | theta _ _, OmegaW => true
  | theta i a, theta j b =>
      decide (i < j) ||
        (decide (i = j) &&
          ((ltbS a b && (E i a).attach.all (fun g => ltbS g.1 (theta j b))) ||
            (E i b).attach.any (fun g => ltbS (theta i a) g.1 || decide (theta i a = g.1))))
  -- principal against sum: `P ≺ ⟨β₀, …⟩` iff `P ≼ β₀`
  | Omega _, sum [] => false
  | Omega i, sum (b :: _) => ltbS (Omega i) b || decide (Omega i = b)
  | OmegaW, sum [] => false
  | OmegaW, sum (b :: _) => ltbS OmegaW b || decide (OmegaW = b)
  | theta _ _, sum [] => false
  | theta i a, sum (b :: _) => ltbS (theta i a) b || decide (theta i a = b)
  -- sum against principal: `⟨⟩ ≺ P`, and `⟨α₀, …⟩ ≺ P` iff `α₀ ≺ P`
  | sum [], Omega _ => true
  | sum (a :: _), Omega j => ltbS a (Omega j)
  | sum [], OmegaW => true
  | sum (a :: _), OmegaW => ltbS a OmegaW
  | sum [], theta _ _ => true
  | sum (a :: _), theta j b => ltbS a (theta j b)
  -- sum against sum: lexicographic
  | sum [], sum [] => false
  | sum [], sum (_ :: _) => true
  | sum (_ :: _), sum [] => false
  | sum (a :: as), sum (b :: bs) => ltbS a b || (decide (a = b) && ltbS (sum as) (sum bs))
termination_by a b => l a + l b
decreasing_by
  all_goals simp only [l_Omega, l_OmegaW, l_theta, l_cons]
  all_goals first
    | omega
    | (have := l_le_of_mem_E g.2; omega)

/-! ### The same order, computed with fuel -/

/-- The order computed with fuel `n` (a structural recursion on `n`, reducible by the kernel). -/
def ltbF : ℕ → ThetaVTerm → ThetaVTerm → Bool
  | 0, _, _ => false
  | _ + 1, Omega i, Omega j => decide (i < j)
  | _ + 1, Omega _, OmegaW => true
  | _ + 1, Omega i, theta j _ => decide (i < j)
  | _ + 1, OmegaW, Omega _ => false
  | _ + 1, OmegaW, OmegaW => false
  | _ + 1, OmegaW, theta _ _ => false
  | _ + 1, theta i _, Omega j => decide (i ≤ j)
  | _ + 1, theta _ _, OmegaW => true
  | n + 1, theta i a, theta j b =>
      decide (i < j) ||
        (decide (i = j) &&
          ((ltbF n a b && (E i a).all (fun g => ltbF n g (theta j b))) ||
            (E i b).any (fun g => ltbF n (theta i a) g || decide (theta i a = g))))
  | _ + 1, Omega _, sum [] => false
  | n + 1, Omega i, sum (b :: _) => ltbF n (Omega i) b || decide (Omega i = b)
  | _ + 1, OmegaW, sum [] => false
  | n + 1, OmegaW, sum (b :: _) => ltbF n OmegaW b || decide (OmegaW = b)
  | _ + 1, theta _ _, sum [] => false
  | n + 1, theta i a, sum (b :: _) => ltbF n (theta i a) b || decide (theta i a = b)
  | _ + 1, sum [], Omega _ => true
  | n + 1, sum (a :: _), Omega j => ltbF n a (Omega j)
  | _ + 1, sum [], OmegaW => true
  | n + 1, sum (a :: _), OmegaW => ltbF n a OmegaW
  | _ + 1, sum [], theta _ _ => true
  | n + 1, sum (a :: _), theta j b => ltbF n a (theta j b)
  | _ + 1, sum [], sum [] => false
  | _ + 1, sum [], sum (_ :: _) => true
  | _ + 1, sum (_ :: _), sum [] => false
  | n + 1, sum (a :: as), sum (b :: bs) =>
      ltbF n a b || (decide (a = b) && ltbF n (sum as) (sum bs))

private theorem all_attach_eq {xs : List ThetaVTerm} {p : ThetaVTerm → Bool}
    {q : {x // x ∈ xs} → Bool} (h : ∀ x (hx : x ∈ xs), p x = q ⟨x, hx⟩) :
    xs.all p = xs.attach.all q := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_attach, true_imp_iff, Subtype.forall]
  exact ⟨fun H x hx => h x hx ▸ H x hx, fun H x hx => (h x hx).symm ▸ H x hx⟩

private theorem any_attach_eq {xs : List ThetaVTerm} {p : ThetaVTerm → Bool}
    {q : {x // x ∈ xs} → Bool} (h : ∀ x (hx : x ∈ xs), p x = q ⟨x, hx⟩) :
    xs.any p = xs.attach.any q := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_attach, true_and, Subtype.exists]
  exact ⟨fun ⟨x, hx, H⟩ => ⟨x, hx, h x hx ▸ H⟩, fun ⟨x, hx, H⟩ => ⟨x, hx, (h x hx).symm ▸ H⟩⟩

/-- With enough fuel, `ltbF` computes the specification `ltbS`. -/
theorem ltbF_eq : ∀ (n : ℕ) (a b : ThetaVTerm), l a + l b < n → ltbF n a b = ltbS a b := by
  intro n
  induction n with
  | zero => intro a b h; omega
  | succ n ih =>
    intro a b h
    rw [ltbS.eq_def]
    match a, b with
    | Omega i, Omega j => rfl
    | Omega _, OmegaW => rfl
    | Omega i, theta j _ => rfl
    | OmegaW, Omega _ => rfl
    | OmegaW, OmegaW => rfl
    | OmegaW, theta _ _ => rfl
    | theta i _, Omega j => rfl
    | theta _ _, OmegaW => rfl
    | theta i a, theta j b =>
      simp only [l_theta] at h
      simp only [ltbF]
      rw [ih a b (by omega)]
      congr 3
      · congr 1
        apply all_attach_eq
        intro g hg
        have := l_le_of_mem_E hg
        exact ih g (theta j b) (by simp; omega)
      · apply any_attach_eq
        intro g hg
        have := l_le_of_mem_E hg
        rw [ih (theta i a) g (by simp; omega)]
    | Omega _, sum [] => rfl
    | Omega i, sum (b :: _) =>
      simp only [ltbF]; rw [ih _ _ (by simp at h ⊢; omega)]
    | OmegaW, sum [] => rfl
    | OmegaW, sum (b :: _) =>
      simp only [ltbF]; rw [ih _ _ (by simp at h ⊢; omega)]
    | theta _ _, sum [] => rfl
    | theta i a, sum (b :: _) =>
      simp only [ltbF]; rw [ih _ _ (by simp at h ⊢; omega)]
    | sum [], Omega _ => rfl
    | sum (a :: _), Omega j =>
      simp only [ltbF]; rw [ih _ _ (by simp at h ⊢; omega)]
    | sum [], OmegaW => rfl
    | sum (a :: _), OmegaW =>
      simp only [ltbF]; rw [ih _ _ (by simp at h ⊢; omega)]
    | sum [], theta _ _ => rfl
    | sum (a :: _), theta j b =>
      simp only [ltbF]; rw [ih _ _ (by simp at h ⊢; omega)]
    | sum [], sum [] => rfl
    | sum [], sum (_ :: _) => rfl
    | sum (_ :: _), sum [] => rfl
    | sum (a :: as), sum (b :: bs) =>
      simp only [ltbF]
      rw [ih a b (by simp at h ⊢; omega), ih (sum as) (sum bs) (by simp at h ⊢; omega)]

/-- The order, computed: `ltbF` with fuel `l α + l β + 1`. -/
def ltb (a b : ThetaVTerm) : Bool := ltbF (l a + l b + 1) a b

theorem ltb_eq_ltbS (a b : ThetaVTerm) : ltb a b = ltbS a b :=
  ltbF_eq _ a b (Nat.lt_succ_self _)

instance : LT ThetaVTerm := ⟨fun a b => ltb a b = true⟩

/-- `α ≼ β` is `α ≺ β ∨ α = β`. -/
instance : LE ThetaVTerm := ⟨fun a b => a < b ∨ a = b⟩

theorem lt_def {a b : ThetaVTerm} : a < b ↔ ltbS a b = true := by
  show ltb a b = true ↔ _
  rw [ltb_eq_ltbS]

theorem le_def {a b : ThetaVTerm} : a ≤ b ↔ a < b ∨ a = b := Iff.rfl

instance decidableLT : DecidableRel (α := ThetaVTerm) (· < ·) :=
  fun a b => inferInstanceAs (Decidable (ltb a b = true))

instance decidableLE : DecidableRel (α := ThetaVTerm) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (a < b ∨ a = b))

theorem le_refl' (a : ThetaVTerm) : a ≤ a := Or.inr rfl

theorem le_of_lt' {a b : ThetaVTerm} (h : a < b) : a ≤ b := Or.inl h

/-! ### The clauses of the order, one constructor pair at a time -/

section Clauses

variable (i j k : ℕ) (a b : ThetaVTerm) (as bs : List ThetaVTerm)

private theorem le_iff_bool {x y : ThetaVTerm} :
    (ltbS x y || decide (x = y)) = true ↔ x ≤ y := by
  simp [le_def, lt_def]

theorem Omega_lt_Omega_iff : Omega i < Omega j ↔ i < j := by
  rw [lt_def, ltbS.eq_def]; simp

theorem Omega_lt_theta_iff : Omega i < theta j b ↔ i < j := by
  rw [lt_def, ltbS.eq_def]; simp

theorem theta_lt_Omega_iff : theta i a < Omega j ↔ i ≤ j := by
  rw [lt_def, ltbS.eq_def]; simp

theorem Omega_lt_OmegaW : Omega i < OmegaW := by
  rw [lt_def, ltbS.eq_def]

theorem theta_lt_OmegaW : theta i a < OmegaW := by
  rw [lt_def, ltbS.eq_def]

theorem not_OmegaW_lt_Omega : ¬ OmegaW < Omega j := by
  rw [lt_def, ltbS.eq_def]; simp

theorem not_OmegaW_lt_OmegaW : ¬ OmegaW < OmegaW := by
  rw [lt_def, ltbS.eq_def]; simp

theorem not_OmegaW_lt_theta : ¬ OmegaW < theta j b := by
  rw [lt_def, ltbS.eq_def]; simp

/-- Collapses of lower level lie below collapses of higher level. -/
theorem theta_lt_theta_of_lt_level {i j : ℕ} (h : i < j) : theta i a < theta j b := by
  rw [lt_def, ltbS.eq_def]; simp [h]

theorem not_theta_lt_theta_of_lt_level {i j : ℕ} (h : j < i) : ¬ theta i a < theta j b := by
  rw [lt_def, ltbS.eq_def]
  simp [Nat.not_lt.mpr (Nat.le_of_lt h), Nat.ne_of_gt h]

/-- The clause at one level: `ϑ_k α ≺ ϑ_k β` iff `α ≺ β` and `E_k(α) ≺* ϑ_k β`, or
`ϑ_k α ≼ δ` for some `δ ∈ E_k(β)`. -/
theorem theta_lt_theta_iff :
    theta k a < theta k b ↔
      (a < b ∧ ∀ g ∈ E k a, g < theta k b) ∨ ∃ g ∈ E k b, theta k a ≤ g := by
  rw [lt_def, ltbS.eq_def]
  simp only [Nat.lt_irrefl, decide_false, decide_true, Bool.false_or, Bool.true_and,
    Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_attach, true_imp_iff, true_and, Subtype.forall, Subtype.exists, decide_eq_true_eq]
  simp only [← lt_def, ← le_def]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨g, hg, h⟩)
    · exact Or.inl ⟨h1, fun g hg => h2 g hg⟩
    · exact Or.inr ⟨g, hg, h⟩
  · rintro (⟨h1, h2⟩ | ⟨g, hg, h⟩)
    · exact Or.inl ⟨h1, fun g hg => h2 g hg⟩
    · exact Or.inr ⟨g, hg, h⟩

theorem not_Omega_lt_nil : ¬ Omega i < sum [] := by
  rw [lt_def, ltbS.eq_def]; simp

theorem Omega_lt_cons_iff : Omega i < sum (b :: bs) ↔ Omega i ≤ b := by
  rw [lt_def, ltbS.eq_def]; exact le_iff_bool

theorem not_OmegaW_lt_nil : ¬ OmegaW < sum [] := by
  rw [lt_def, ltbS.eq_def]; simp

theorem OmegaW_lt_cons_iff : OmegaW < sum (b :: bs) ↔ OmegaW ≤ b := by
  rw [lt_def, ltbS.eq_def]; exact le_iff_bool

theorem not_theta_lt_nil : ¬ theta i a < sum [] := by
  rw [lt_def, ltbS.eq_def]; simp

theorem theta_lt_cons_iff : theta i a < sum (b :: bs) ↔ theta i a ≤ b := by
  rw [lt_def, ltbS.eq_def]; exact le_iff_bool

theorem nil_lt_Omega : sum [] < Omega j := by
  rw [lt_def, ltbS.eq_def]

theorem cons_lt_Omega_iff : sum (a :: as) < Omega j ↔ a < Omega j := by
  rw [lt_def, ltbS.eq_def, lt_def]

theorem nil_lt_OmegaW : sum [] < OmegaW := by
  rw [lt_def, ltbS.eq_def]

theorem cons_lt_OmegaW_iff : sum (a :: as) < OmegaW ↔ a < OmegaW := by
  rw [lt_def, ltbS.eq_def, lt_def]

theorem nil_lt_theta : sum [] < theta j b := by
  rw [lt_def, ltbS.eq_def]

theorem cons_lt_theta_iff : sum (a :: as) < theta j b ↔ a < theta j b := by
  rw [lt_def, ltbS.eq_def, lt_def]

theorem not_nil_lt_nil : ¬ sum [] < sum [] := by
  rw [lt_def, ltbS.eq_def]; simp

/-- A proper prefix is smaller. -/
theorem nil_lt_cons : sum [] < sum (b :: bs) := by
  rw [lt_def, ltbS.eq_def]

theorem not_cons_lt_nil : ¬ sum (a :: as) < sum [] := by
  rw [lt_def, ltbS.eq_def]; simp

/-- Lexicographic comparison of sums, one entry at a time. -/
theorem cons_lt_cons_iff :
    sum (a :: as) < sum (b :: bs) ↔ a < b ∨ (a = b ∧ sum as < sum bs) := by
  rw [lt_def, ltbS.eq_def]
  simp [lt_def]

end Clauses

/-- `P ≺ ⟨⟩` never holds for principal `P`. -/
theorem not_prin_lt_nil {p : ThetaVTerm} (hp : IsPrin p) : ¬ p < sum [] := by
  cases p with
  | Omega i => exact not_Omega_lt_nil i
  | OmegaW => exact not_OmegaW_lt_nil
  | theta i a => exact not_theta_lt_nil i a
  | sum _ => exact absurd hp id

/-- `P ≺ ⟨β₀, …⟩ ↔ P ≼ β₀` for principal `P`. -/
theorem prin_lt_cons_iff {p b : ThetaVTerm} {bs : List ThetaVTerm} (hp : IsPrin p) :
    p < sum (b :: bs) ↔ p ≤ b := by
  cases p with
  | Omega i => exact Omega_lt_cons_iff i b bs
  | OmegaW => exact OmegaW_lt_cons_iff b bs
  | theta i a => exact theta_lt_cons_iff i a b bs
  | sum _ => exact absurd hp id

/-- `⟨⟩ ≺ P` for principal `P`. -/
theorem nil_lt_prin {p : ThetaVTerm} (hp : IsPrin p) : sum [] < p := by
  cases p with
  | Omega j => exact nil_lt_Omega j
  | OmegaW => exact nil_lt_OmegaW
  | theta j b => exact nil_lt_theta j b
  | sum _ => exact absurd hp id

/-- `⟨α₀, …⟩ ≺ P ↔ α₀ ≺ P` for principal `P`. -/
theorem cons_lt_prin_iff {p a : ThetaVTerm} {as : List ThetaVTerm} (hp : IsPrin p) :
    sum (a :: as) < p ↔ a < p := by
  cases p with
  | Omega j => exact cons_lt_Omega_iff j a as
  | OmegaW => exact cons_lt_OmegaW_iff a as
  | theta j b => exact cons_lt_theta_iff j a b as
  | sum _ => exact absurd hp id

/-- Every principal term other than `Ω_ω` lies below `Ω_ω`. -/
theorem lt_OmegaW_of_isPrinB {p : ThetaVTerm} (hp : IsPrinB p) : p < OmegaW := by
  cases p with
  | Omega i => exact Omega_lt_OmegaW i
  | OmegaW => exact absurd hp id
  | theta i a => exact theta_lt_OmegaW i a
  | sum _ => exact absurd hp id

/-- No principal term lies above `Ω_ω`. -/
theorem not_OmegaW_lt_prin {q : ThetaVTerm} (hq : IsPrin q) : ¬ OmegaW < q := by
  cases q with
  | Omega j => exact not_OmegaW_lt_Omega j
  | OmegaW => exact not_OmegaW_lt_OmegaW
  | theta j b => exact not_OmegaW_lt_theta j b
  | sum _ => exact absurd hq id

/-! ### The comparison function -/

/-- Three-way comparison: `.eq` on equal terms, `.lt` when `a ≺ b`, `.gt` otherwise. -/
def cmp (a b : ThetaVTerm) : Ordering :=
  if a = b then .eq else if a < b then .lt else .gt

@[simp] theorem cmp_refl (a : ThetaVTerm) : cmp a a = .eq := by simp [cmp]

theorem cmp_eq_eq_iff {a b : ThetaVTerm} : cmp a b = .eq ↔ a = b := by
  unfold cmp; split_ifs <;> simp_all

/-! ### Normal form

As in `ThetaW/Basic`: in `⟨α₀, …, α_{n-1}⟩` we have `α_{n-1} ≼ ⋯ ≼ α₀`, and if `n = 1` then
`α₀` is not principal; hereditarily. -/

/-- The entries of a list are non-increasing. -/
def Desc : List ThetaVTerm → Prop
  | [] => True
  | [_] => True
  | x :: y :: ys => y ≤ x ∧ Desc (y :: ys)

instance decidableDesc : DecidablePred Desc
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | x :: y :: ys =>
    haveI := decidableDesc (y :: ys)
    inferInstanceAs (Decidable (y ≤ x ∧ Desc (y :: ys)))

@[simp] theorem desc_nil : Desc [] := trivial
@[simp] theorem desc_singleton (x : ThetaVTerm) : Desc [x] := trivial
@[simp] theorem desc_cons_cons (x y : ThetaVTerm) (ys : List ThetaVTerm) :
    Desc (x :: y :: ys) ↔ y ≤ x ∧ Desc (y :: ys) := Iff.rfl

theorem Desc.tail {x : ThetaVTerm} {xs : List ThetaVTerm} (h : Desc (x :: xs)) : Desc xs := by
  cases xs with
  | nil => trivial
  | cons y ys => exact h.2

/-- A one-entry sum `⟨α₀⟩` must not have `α₀` principal. -/
def SingleOK : List ThetaVTerm → Prop
  | [x] => ¬ IsPrin x
  | _ => True

instance decidableSingleOK : DecidablePred SingleOK
  | [] => isTrue trivial
  | [x] => inferInstanceAs (Decidable (¬ IsPrin x))
  | _ :: _ :: _ => isTrue trivial

mutual
/-- The normal form. -/
def NF : ThetaVTerm → Prop
  | Omega _ => True
  | OmegaW => True
  | theta _ a => NF a
  | sum xs => NFList xs ∧ Desc xs ∧ SingleOK xs
/-- Every entry of the list is in normal form. -/
def NFList : List ThetaVTerm → Prop
  | [] => True
  | x :: xs => NF x ∧ NFList xs
end

mutual
/-- A decision procedure for `NF`. -/
def decNF : (a : ThetaVTerm) → Decidable (NF a)
  | Omega _ => isTrue (by simp [NF])
  | OmegaW => isTrue (by simp [NF])
  | theta _ a =>
    match decNF a with
    | isTrue h => isTrue (by simpa [NF] using h)
    | isFalse h => isFalse (by simpa [NF] using h)
  | sum xs =>
    match decNFList xs with
    | isTrue h =>
      if hd : Desc xs ∧ SingleOK xs then isTrue (by simp only [NF]; exact ⟨h, hd⟩)
      else isFalse (by simp only [NF]; exact fun h' => hd h'.2)
    | isFalse h => isFalse (by simp only [NF]; exact fun h' => h h'.1)
/-- A decision procedure for `NFList`. -/
def decNFList : (xs : List ThetaVTerm) → Decidable (NFList xs)
  | [] => isTrue (by simp [NFList])
  | x :: xs =>
    match decNF x, decNFList xs with
    | isTrue h1, isTrue h2 => isTrue (by simp only [NFList]; exact ⟨h1, h2⟩)
    | isFalse h1, _ => isFalse (by simp only [NFList]; exact fun h => h1 h.1)
    | _, isFalse h2 => isFalse (by simp only [NFList]; exact fun h => h2 h.2)
end

instance : DecidablePred NF := decNF

@[simp] theorem nf_Omega (k : ℕ) : NF (Omega k) := by simp [NF]

@[simp] theorem nf_OmegaW : NF OmegaW := by simp [NF]

@[simp] theorem nf_theta_iff (k : ℕ) (a : ThetaVTerm) : NF (theta k a) ↔ NF a := by simp [NF]

theorem nfList_iff {xs : List ThetaVTerm} : NFList xs ↔ ∀ x ∈ xs, NF x := by
  induction xs with
  | nil => simp [NFList]
  | cons y ys ih => simp [NFList, ih]

theorem nf_sum_iff (xs : List ThetaVTerm) :
    NF (sum xs) ↔ (∀ x ∈ xs, NF x) ∧ Desc xs ∧ SingleOK xs := by
  simp only [NF, nfList_iff]

theorem NF.of_mem {x : ThetaVTerm} {xs : List ThetaVTerm} (h : NF (sum xs)) (hx : x ∈ xs) :
    NF x :=
  ((nf_sum_iff xs).mp h).1 x hx

theorem NF.theta_arg {k : ℕ} {a : ThetaVTerm} (h : NF (theta k a)) : NF a :=
  (nf_theta_iff k a).mp h

theorem NF.desc {xs : List ThetaVTerm} (h : NF (sum xs)) : Desc xs := ((nf_sum_iff xs).mp h).2.1

theorem nf_zero : NF zero := by simp [zero, nf_sum_iff, SingleOK]

/-- The elements of `E_k(α)` of a normal term are normal. -/
theorem NF.of_mem_E {k : ℕ} : ∀ {a g : ThetaVTerm}, NF a → g ∈ E k a → NF g
  | Omega _, g, _, h => by simp at h
  | OmegaW, g, _, h => by simp at h
  | theta j a, g, ha, h => by
    by_cases hj : j ≤ k
    · rw [E_theta_of_le hj] at h; simp at h; exact h ▸ ha
    · rw [E_theta_of_lt (Nat.lt_of_not_le hj)] at h
      exact NF.of_mem_E ha.theta_arg h
  | sum xs, g, ha, h => by
    obtain ⟨x, hx, hg⟩ := mem_E_sum.mp h
    exact NF.of_mem_E (ha.of_mem hx) hg
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hx

/-! ### Terms without `Ω_ω` -/

mutual
/-- `WFree α`: `Ω_ω` does not occur in `α`. -/
def WFree : ThetaVTerm → Prop
  | Omega _ => True
  | OmegaW => False
  | theta _ a => WFree a
  | sum xs => WFreeList xs
/-- Every entry of the list is `Ω_ω`-free. -/
def WFreeList : List ThetaVTerm → Prop
  | [] => True
  | x :: xs => WFree x ∧ WFreeList xs
end

@[simp] theorem wFree_Omega (k : ℕ) : WFree (Omega k) := by simp [WFree]

@[simp] theorem not_wFree_OmegaW : ¬ WFree OmegaW := by simp [WFree]

@[simp] theorem wFree_theta_iff (k : ℕ) (a : ThetaVTerm) : WFree (theta k a) ↔ WFree a := by
  simp [WFree]

theorem wFreeList_iff {xs : List ThetaVTerm} : WFreeList xs ↔ ∀ x ∈ xs, WFree x := by
  induction xs with
  | nil => simp [WFreeList]
  | cons y ys ih => simp [WFreeList, ih]

theorem wFree_sum_iff (xs : List ThetaVTerm) : WFree (sum xs) ↔ ∀ x ∈ xs, WFree x := by
  simp only [WFree, wFreeList_iff]

/-- The elements of `E_k(α)` of an `Ω_ω`-free term are `Ω_ω`-free. -/
theorem WFree.of_mem_E {k : ℕ} : ∀ {a g : ThetaVTerm}, WFree a → g ∈ E k a → WFree g
  | Omega _, g, _, h => by simp at h
  | OmegaW, g, _, h => by simp at h
  | theta j a, g, ha, h => by
    by_cases hj : j ≤ k
    · rw [E_theta_of_le hj] at h; simp at h; exact h ▸ ha
    · rw [E_theta_of_lt (Nat.lt_of_not_le hj)] at h
      exact WFree.of_mem_E ((wFree_theta_iff j a).mp ha) h
  | sum xs, g, ha, h => by
    obtain ⟨x, hx, hg⟩ := mem_E_sum.mp h
    exact WFree.of_mem_E ((wFree_sum_iff xs).mp ha x hx) hg
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hx

end ThetaVTerm

end OrdinalAnalysis
