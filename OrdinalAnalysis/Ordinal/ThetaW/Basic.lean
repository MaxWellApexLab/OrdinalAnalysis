/-
  The ϑ-notation with finitely many levels: terms, length, the level-`k` coefficient sets,
  the order, and the normal form.

  Sources.
  * A. Freund, *Impredicativity and trees with gap condition: a second course on ordinal
    analysis*, arXiv:2204.09321, Definition 3.1: the one-level system (`Ω`, `ϑ`, Cantor
    sums), its order, and its normal form.  The present system has one copy of that
    construction per level.
  * G. Wilken, *Fundamental sequences based on localization*, arXiv:2410.15953, §2.1,
    Proposition 2.3 (Lemma 3.30 of G. Wilken, *Ordinal arithmetic based on Skolem hulling*,
    Ann. Pure Appl. Logic 145 (2007)): for the stepwise defined functions
    `ϑ_j : Ω_{j+2} → Ω_{j+1}`,
      `ϑ_j(α) < ϑ_j(γ) ⇔ (α < γ ∧ α^{⋆j} < ϑ_j(γ)) ∨ ϑ_j(α) ≤ γ^{⋆j}`,
    where `α^{⋆j}` is the largest `ϑ_j`-subterm of `α`, the `ϑ_i`-subterms with `i < j` being
    treated as atoms (and `0` if there is none).

  Terms.  For every level `k : ℕ`:
  * `Omega k` denotes `Ω_{k+1}` (so `Omega 0` is `Ω₁`; there is no term for `Ω₀ = 0`);
  * `theta k α` denotes `ϑ_k α`, an ε-number in the interval `(Ω_k, Ω_{k+1})`;
  * `sum [α₀, …, α_{n-1}]` denotes the Cantor sum `ω^α₀ + ⋯ + ω^α_{n-1}`.
  The arguments of `ϑ_k` are unrestricted (as in Freund's one-level system, where `ϑ` is
  applied to all terms below `ε_{Ω+1}`), not bounded by `Ω_{k+2}` as in Wilken's system.

  The level-`k` coefficient set `E_k(α)` collects the maximal subterms `ϑ_j δ` of `α` with
  `j ≤ k`, looking through the collapses of level `> k`:
    `E_k(Ω_{j+1}) = ∅`,  `E_k(ϑ_j δ) = {ϑ_j δ}` if `j ≤ k` and `E_k(δ)` otherwise,
    `E_k(⟨α₀, …⟩) = ⋃ E_k(α_i)`.
  These are the terms of `α` that lie below `Ω_{k+1}` and are not built up from smaller
  terms by `+`, `ω^·`, the `Ω`'s and the collapses of higher level.  The members of level
  `< k` lie below `Ω_k`, hence below every `ϑ_k`-term; so `∀ δ ∈ E_k(α), δ < ϑ_k γ` says
  `α^{⋆k} < ϑ_k(γ)`, and `∃ δ ∈ E_k(γ), ϑ_k α ≤ δ` says `ϑ_k α ≤ γ^{⋆k}`.

  The order `≺`, on all raw terms, by recursion on `l α + l β`:
  * principal terms are compared by position first: `ϑ_i α ≺ Ω_{j+1}` iff `i ≤ j`,
    `Ω_{i+1} ≺ ϑ_j β` iff `i < j`, `Ω_{i+1} ≺ Ω_{j+1}` iff `i < j`, and `ϑ_i α ≺ ϑ_j β`
    whenever `i < j`;
  * at one level, the clause of Freund, Definition 3.1 (ii'), with `E_k` in place of `E`:
    `ϑ_k α ≺ ϑ_k β  ⇔  (α ≺ β ∧ E_k(α) ≺* ϑ_k β) ∨ ∃ δ ∈ E_k(β). ϑ_k α ≼ δ`
    (the clause of Wilken, Proposition 2.3, in the form just described);
  * a principal term against a sum, and sums against sums, exactly as in Freund,
    Definition 3.1 (i'), (iii').
  The normal form is Freund's: the entries of a sum are non-increasing, and a one-entry sum
  `⟨α₀⟩` does not have `α₀` principal, hereditarily.

  The order is linear on all terms, for all levels at once.  It is well founded on the
  normal terms with a bound on the levels (proved for two levels), but not on the normal
  terms of all levels: `ϑ₀(Ω₂) ≻ ϑ₀(ϑ₁(Ω₃)) ≻ ϑ₀(ϑ₁(ϑ₂(Ω₄))) ≻ ⋯` is a descending sequence.
-/
import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace OrdinalAnalysis

/-- Raw terms of the multi-level ϑ-notation: `Omega k` is `Ω_{k+1}`, `theta k α` is `ϑ_k α`,
and `sum [α₀, …, α_{n-1}]` is `⟨α₀, …, α_{n-1}⟩`. -/
inductive ThetaWTerm : Type
  | Omega : ℕ → ThetaWTerm
  | theta : ℕ → ThetaWTerm → ThetaWTerm
  | sum : List ThetaWTerm → ThetaWTerm
  deriving Repr

namespace ThetaWTerm

/-! ### Decidable equality -/

mutual
/-- Decidable equality of terms, by structural recursion. -/
def decEq : (a b : ThetaWTerm) → Decidable (a = b)
  | Omega i, Omega j =>
    if h : i = j then isTrue (h ▸ rfl) else isFalse (fun e => h (Omega.inj e))
  | Omega _, theta _ _ => isFalse (fun h => ThetaWTerm.noConfusion h)
  | Omega _, sum _ => isFalse (fun h => ThetaWTerm.noConfusion h)
  | theta _ _, Omega _ => isFalse (fun h => ThetaWTerm.noConfusion h)
  | theta i a, theta j b =>
    if h : i = j then
      match decEq a b with
      | isTrue h' => isTrue (h ▸ h' ▸ rfl)
      | isFalse h' => isFalse (fun e => h' (theta.inj e).2)
    else isFalse (fun e => h (theta.inj e).1)
  | theta _ _, sum _ => isFalse (fun h => ThetaWTerm.noConfusion h)
  | sum _, Omega _ => isFalse (fun h => ThetaWTerm.noConfusion h)
  | sum _, theta _ _ => isFalse (fun h => ThetaWTerm.noConfusion h)
  | sum xs, sum ys =>
    match decEqList xs ys with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => h (sum.inj e))
/-- Decidable equality of lists of terms, by structural recursion. -/
def decEqList : (xs ys : List ThetaWTerm) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | x :: xs, y :: ys =>
    match decEq x y, decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h1, _ => isFalse (fun e => h1 (List.cons.inj e).1)
    | _, isFalse h2 => isFalse (fun e => h2 (List.cons.inj e).2)
end

instance : DecidableEq ThetaWTerm := decEq

/-- The term `0 = ⟨⟩`. -/
def zero : ThetaWTerm := sum []

/-- `Ω_{k+1}` and the terms `ϑ_k α` are the principal terms (they denote ε-numbers). -/
def IsPrin : ThetaWTerm → Prop
  | Omega _ => True
  | theta _ _ => True
  | sum _ => False

instance : DecidablePred IsPrin := fun a =>
  match a with
  | Omega _ => isTrue trivial
  | theta _ _ => isTrue trivial
  | sum _ => isFalse id

@[simp] theorem isPrin_Omega (k : ℕ) : IsPrin (Omega k) := trivial
@[simp] theorem isPrin_theta (k : ℕ) (a : ThetaWTerm) : IsPrin (theta k a) := trivial
@[simp] theorem not_isPrin_sum (xs : List ThetaWTerm) : ¬ IsPrin (sum xs) := id

/-- The position of a principal term among the principal terms: `ϑ_k`-terms have position
`2k`, and `Ω_{k+1}` has position `2k + 1` (it lies above every `ϑ_k`-term and below every
`ϑ_{k+1}`-term).  The value on sums is irrelevant. -/
def key : ThetaWTerm → ℕ
  | Omega k => 2 * k + 1
  | theta k _ => 2 * k
  | sum _ => 0

@[simp] theorem key_Omega (k : ℕ) : key (Omega k) = 2 * k + 1 := rfl
@[simp] theorem key_theta (k : ℕ) (a : ThetaWTerm) : key (theta k a) = 2 * k := rfl

/-! ### Length -/

mutual
/-- The length function: `l(Ω_{k+1}) = 0`, `l(ϑ_k α) = l(α) + 1`,
`l(⟨α₀, …, α_{n-1}⟩) = n + Σ l(α_i)` (Freund, after Definition 3.1). -/
def l : ThetaWTerm → ℕ
  | Omega _ => 0
  | theta _ a => l a + 1
  | sum xs => lList xs
/-- `lList [α₀, …, α_{n-1}] = n + Σ l(α_i)`. -/
def lList : List ThetaWTerm → ℕ
  | [] => 0
  | x :: xs => l x + 1 + lList xs
end

@[simp] theorem l_Omega (k : ℕ) : l (Omega k) = 0 := by simp [l]
@[simp] theorem l_theta (k : ℕ) (a : ThetaWTerm) : l (theta k a) = l a + 1 := by simp [l]
@[simp] theorem l_nil : l (sum []) = 0 := by simp [l, lList]
@[simp] theorem l_cons (x : ThetaWTerm) (xs : List ThetaWTerm) :
    l (sum (x :: xs)) = l x + 1 + l (sum xs) := by simp [l, lList]

theorem l_lt_of_mem {x : ThetaWTerm} {xs : List ThetaWTerm} (h : x ∈ xs) :
    l x < l (sum xs) := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp; omega
    · have := ih h; simp; omega

/-! ### The level-`k` coefficient sets `E_k` -/

mutual
/-- The level-`k` coefficient set `E_k(α)`, as a list: `E_k(Ω_{j+1}) = ∅`,
`E_k(ϑ_j δ) = {ϑ_j δ}` for `j ≤ k`, `E_k(ϑ_j δ) = E_k(δ)` for `j > k`, and
`E_k(⟨α₀, …, α_{n-1}⟩) = ⋃ E_k(α_i)`. -/
def E (k : ℕ) : ThetaWTerm → List ThetaWTerm
  | Omega _ => []
  | theta j a => if j ≤ k then [theta j a] else E k a
  | sum xs => EList k xs
/-- The union of the `E_k(α_i)` over a list. -/
def EList (k : ℕ) : List ThetaWTerm → List ThetaWTerm
  | [] => []
  | x :: xs => E k x ++ EList k xs
end

@[simp] theorem E_Omega (k j : ℕ) : E k (Omega j) = [] := by simp [E]

theorem E_theta_of_le {k j : ℕ} (h : j ≤ k) (a : ThetaWTerm) :
    E k (theta j a) = [theta j a] := by simp [E, h]

theorem E_theta_of_lt {k j : ℕ} (h : k < j) (a : ThetaWTerm) :
    E k (theta j a) = E k a := by simp [E, Nat.not_le.mpr h]

@[simp] theorem E_nil (k : ℕ) : E k (sum []) = [] := by simp [E, EList]

@[simp] theorem E_cons (k : ℕ) (x : ThetaWTerm) (xs : List ThetaWTerm) :
    E k (sum (x :: xs)) = E k x ++ E k (sum xs) := by simp [E, EList]

theorem mem_E_sum {k : ℕ} {g : ThetaWTerm} {xs : List ThetaWTerm} :
    g ∈ E k (sum xs) ↔ ∃ x ∈ xs, g ∈ E k x := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp [ih]

theorem mem_E_of_mem {k : ℕ} {x g : ThetaWTerm} {xs : List ThetaWTerm} (hx : x ∈ xs)
    (hg : g ∈ E k x) : g ∈ E k (sum xs) :=
  mem_E_sum.mpr ⟨x, hx, hg⟩

/-- `δ ∈ E_k(α)` implies `l(δ) ≤ l(α)`. -/
theorem l_le_of_mem_E {k : ℕ} : ∀ {a g : ThetaWTerm}, g ∈ E k a → l g ≤ l a
  | Omega _, g, h => by simp at h
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
    ∀ {a g : ThetaWTerm}, g ∈ E k a → ∃ j d, j ≤ k ∧ g = theta j d
  | Omega _, g, h => by simp at h
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

/-! ### The order

The relation `α ≺ β`, computed by recursion on `l α + l β`.  In the clauses, `α ≼ β`
abbreviates `α ≺ β ∨ α = β`; the lexicographic clause for two sums is unfolded one entry at a
time, as in the one-level system. -/

/-- The multi-level ϑ-order, as a boolean function (clauses in the module docstring). -/
def ltb : ThetaWTerm → ThetaWTerm → Bool
  -- principal against principal: position first
  | Omega i, Omega j => decide (i < j)
  | Omega i, theta j _ => decide (i < j)
  | theta i _, Omega j => decide (i ≤ j)
  | theta i a, theta j b =>
      decide (i < j) ||
        (decide (i = j) &&
          ((ltb a b && (E i a).attach.all (fun g => ltb g.1 (theta j b))) ||
            (E i b).attach.any (fun g => ltb (theta i a) g.1 || decide (theta i a = g.1))))
  -- principal against sum: `P ≺ ⟨β₀, …⟩` iff `P ≼ β₀`
  | Omega _, sum [] => false
  | Omega i, sum (b :: _) => ltb (Omega i) b || decide (Omega i = b)
  | theta _ _, sum [] => false
  | theta i a, sum (b :: _) => ltb (theta i a) b || decide (theta i a = b)
  -- sum against principal: `⟨⟩ ≺ P`, and `⟨α₀, …⟩ ≺ P` iff `α₀ ≺ P`
  | sum [], Omega _ => true
  | sum (a :: _), Omega j => ltb a (Omega j)
  | sum [], theta _ _ => true
  | sum (a :: _), theta j b => ltb a (theta j b)
  -- sum against sum: lexicographic
  | sum [], sum [] => false
  | sum [], sum (_ :: _) => true
  | sum (_ :: _), sum [] => false
  | sum (a :: as), sum (b :: bs) => ltb a b || (decide (a = b) && ltb (sum as) (sum bs))
termination_by a b => l a + l b
decreasing_by
  all_goals simp only [l_Omega, l_theta, l_cons]
  all_goals first
    | omega
    | (have := l_le_of_mem_E g.2; omega)

instance : LT ThetaWTerm := ⟨fun a b => ltb a b = true⟩

/-- `α ≼ β` is `α ≺ β ∨ α = β`. -/
instance : LE ThetaWTerm := ⟨fun a b => a < b ∨ a = b⟩

theorem lt_def {a b : ThetaWTerm} : a < b ↔ ltb a b = true := Iff.rfl

theorem le_def {a b : ThetaWTerm} : a ≤ b ↔ a < b ∨ a = b := Iff.rfl

instance decidableLT : DecidableRel (α := ThetaWTerm) (· < ·) :=
  fun a b => inferInstanceAs (Decidable (ltb a b = true))

instance decidableLE : DecidableRel (α := ThetaWTerm) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (a < b ∨ a = b))

theorem le_refl' (a : ThetaWTerm) : a ≤ a := Or.inr rfl

theorem le_of_lt' {a b : ThetaWTerm} (h : a < b) : a ≤ b := Or.inl h

/-! ### The clauses of the order, one constructor pair at a time -/

section Clauses

variable (i j k : ℕ) (a b : ThetaWTerm) (as bs : List ThetaWTerm)

private theorem le_iff_bool {x y : ThetaWTerm} :
    (ltb x y || decide (x = y)) = true ↔ x ≤ y := by
  simp [le_def, lt_def]

theorem Omega_lt_Omega_iff : Omega i < Omega j ↔ i < j := by
  rw [lt_def, ltb.eq_def]; simp

theorem Omega_lt_theta_iff : Omega i < theta j b ↔ i < j := by
  rw [lt_def, ltb.eq_def]; simp

theorem theta_lt_Omega_iff : theta i a < Omega j ↔ i ≤ j := by
  rw [lt_def, ltb.eq_def]; simp

/-- Collapses of lower level lie below collapses of higher level. -/
theorem theta_lt_theta_of_lt_level {i j : ℕ} (h : i < j) : theta i a < theta j b := by
  rw [lt_def, ltb.eq_def]; simp [h]

theorem not_theta_lt_theta_of_lt_level {i j : ℕ} (h : j < i) : ¬ theta i a < theta j b := by
  rw [lt_def, ltb.eq_def]
  simp [Nat.not_lt.mpr (Nat.le_of_lt h), Nat.ne_of_gt h]

/-- The clause at one level: `ϑ_k α ≺ ϑ_k β` iff `α ≺ β` and `E_k(α) ≺* ϑ_k β`, or
`ϑ_k α ≼ δ` for some `δ ∈ E_k(β)` (Freund, Definition 3.1 (ii'), with `E_k`; Wilken,
arXiv:2410.15953, Proposition 2.3). -/
theorem theta_lt_theta_iff :
    theta k a < theta k b ↔
      (a < b ∧ ∀ g ∈ E k a, g < theta k b) ∨ ∃ g ∈ E k b, theta k a ≤ g := by
  rw [lt_def, ltb.eq_def]
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
  rw [lt_def, ltb.eq_def]; simp

theorem Omega_lt_cons_iff : Omega i < sum (b :: bs) ↔ Omega i ≤ b := by
  rw [lt_def, ltb.eq_def]; exact le_iff_bool

theorem not_theta_lt_nil : ¬ theta i a < sum [] := by
  rw [lt_def, ltb.eq_def]; simp

theorem theta_lt_cons_iff : theta i a < sum (b :: bs) ↔ theta i a ≤ b := by
  rw [lt_def, ltb.eq_def]; exact le_iff_bool

theorem nil_lt_Omega : sum [] < Omega j := by
  rw [lt_def, ltb.eq_def]

theorem cons_lt_Omega_iff : sum (a :: as) < Omega j ↔ a < Omega j := by
  rw [lt_def, ltb.eq_def]; rfl

theorem nil_lt_theta : sum [] < theta j b := by
  rw [lt_def, ltb.eq_def]

theorem cons_lt_theta_iff : sum (a :: as) < theta j b ↔ a < theta j b := by
  rw [lt_def, ltb.eq_def]; rfl

theorem not_nil_lt_nil : ¬ sum [] < sum [] := by
  rw [lt_def, ltb.eq_def]; simp

/-- A proper prefix is smaller. -/
theorem nil_lt_cons : sum [] < sum (b :: bs) := by
  rw [lt_def, ltb.eq_def]

theorem not_cons_lt_nil : ¬ sum (a :: as) < sum [] := by
  rw [lt_def, ltb.eq_def]; simp

/-- Lexicographic comparison of sums, one entry at a time. -/
theorem cons_lt_cons_iff :
    sum (a :: as) < sum (b :: bs) ↔ a < b ∨ (a = b ∧ sum as < sum bs) := by
  rw [lt_def, ltb.eq_def]
  simp [lt_def]

end Clauses

/-- `P ≺ ⟨⟩` never holds for principal `P`. -/
theorem not_prin_lt_nil {p : ThetaWTerm} (hp : IsPrin p) : ¬ p < sum [] := by
  cases p with
  | Omega i => exact not_Omega_lt_nil i
  | theta i a => exact not_theta_lt_nil i a
  | sum _ => exact absurd hp id

/-- `P ≺ ⟨β₀, …⟩ ↔ P ≼ β₀` for principal `P`. -/
theorem prin_lt_cons_iff {p b : ThetaWTerm} {bs : List ThetaWTerm} (hp : IsPrin p) :
    p < sum (b :: bs) ↔ p ≤ b := by
  cases p with
  | Omega i => exact Omega_lt_cons_iff i b bs
  | theta i a => exact theta_lt_cons_iff i a b bs
  | sum _ => exact absurd hp id

/-- `⟨⟩ ≺ P` for principal `P`. -/
theorem nil_lt_prin {p : ThetaWTerm} (hp : IsPrin p) : sum [] < p := by
  cases p with
  | Omega j => exact nil_lt_Omega j
  | theta j b => exact nil_lt_theta j b
  | sum _ => exact absurd hp id

/-- `⟨α₀, …⟩ ≺ P ↔ α₀ ≺ P` for principal `P`. -/
theorem cons_lt_prin_iff {p a : ThetaWTerm} {as : List ThetaWTerm} (hp : IsPrin p) :
    sum (a :: as) < p ↔ a < p := by
  cases p with
  | Omega j => exact cons_lt_Omega_iff j a as
  | theta j b => exact cons_lt_theta_iff j a b as
  | sum _ => exact absurd hp id

/-! ### The comparison function -/

/-- Three-way comparison: `.eq` on equal terms, `.lt` when `a ≺ b`, `.gt` otherwise.  That
`.gt` means `b ≺ a` is the totality of the order, proved in the companion module. -/
def cmp (a b : ThetaWTerm) : Ordering :=
  if a = b then .eq else if a < b then .lt else .gt

@[simp] theorem cmp_refl (a : ThetaWTerm) : cmp a a = .eq := by simp [cmp]

theorem cmp_eq_eq_iff {a b : ThetaWTerm} : cmp a b = .eq ↔ a = b := by
  unfold cmp; split_ifs <;> simp_all

/-! ### Normal form

As in Freund, Definition 3.1 (iii): in `⟨α₀, …, α_{n-1}⟩` we have `α_{n-1} ≼ ⋯ ≼ α₀`, and if
`n = 1` then `α₀` is not principal; the conditions apply hereditarily.  No condition is
imposed on the argument of `ϑ_k` beyond its own normal form. -/

/-- The entries of a list are non-increasing. -/
def Desc : List ThetaWTerm → Prop
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
@[simp] theorem desc_singleton (x : ThetaWTerm) : Desc [x] := trivial
@[simp] theorem desc_cons_cons (x y : ThetaWTerm) (ys : List ThetaWTerm) :
    Desc (x :: y :: ys) ↔ y ≤ x ∧ Desc (y :: ys) := Iff.rfl

theorem Desc.tail {x : ThetaWTerm} {xs : List ThetaWTerm} (h : Desc (x :: xs)) : Desc xs := by
  cases xs with
  | nil => trivial
  | cons y ys => exact h.2

/-- A one-entry sum `⟨α₀⟩` must not have `α₀` principal. -/
def SingleOK : List ThetaWTerm → Prop
  | [x] => ¬ IsPrin x
  | _ => True

instance decidableSingleOK : DecidablePred SingleOK
  | [] => isTrue trivial
  | [x] => inferInstanceAs (Decidable (¬ IsPrin x))
  | _ :: _ :: _ => isTrue trivial

mutual
/-- The normal form. -/
def NF : ThetaWTerm → Prop
  | Omega _ => True
  | theta _ a => NF a
  | sum xs => NFList xs ∧ Desc xs ∧ SingleOK xs
/-- Every entry of the list is in normal form. -/
def NFList : List ThetaWTerm → Prop
  | [] => True
  | x :: xs => NF x ∧ NFList xs
end

mutual
/-- A decision procedure for `NF`. -/
def decNF : (a : ThetaWTerm) → Decidable (NF a)
  | Omega _ => isTrue (by simp [NF])
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
def decNFList : (xs : List ThetaWTerm) → Decidable (NFList xs)
  | [] => isTrue (by simp [NFList])
  | x :: xs =>
    match decNF x, decNFList xs with
    | isTrue h1, isTrue h2 => isTrue (by simp only [NFList]; exact ⟨h1, h2⟩)
    | isFalse h1, _ => isFalse (by simp only [NFList]; exact fun h => h1 h.1)
    | _, isFalse h2 => isFalse (by simp only [NFList]; exact fun h => h2 h.2)
end

instance : DecidablePred NF := decNF

@[simp] theorem nf_Omega (k : ℕ) : NF (Omega k) := by simp [NF]

@[simp] theorem nf_theta_iff (k : ℕ) (a : ThetaWTerm) : NF (theta k a) ↔ NF a := by simp [NF]

theorem nfList_iff {xs : List ThetaWTerm} : NFList xs ↔ ∀ x ∈ xs, NF x := by
  induction xs with
  | nil => simp [NFList]
  | cons y ys ih => simp [NFList, ih]

theorem nf_sum_iff (xs : List ThetaWTerm) :
    NF (sum xs) ↔ (∀ x ∈ xs, NF x) ∧ Desc xs ∧ SingleOK xs := by
  simp only [NF, nfList_iff]

theorem NF.of_mem {x : ThetaWTerm} {xs : List ThetaWTerm} (h : NF (sum xs)) (hx : x ∈ xs) :
    NF x :=
  ((nf_sum_iff xs).mp h).1 x hx

theorem NF.theta_arg {k : ℕ} {a : ThetaWTerm} (h : NF (theta k a)) : NF a :=
  (nf_theta_iff k a).mp h

theorem NF.desc {xs : List ThetaWTerm} (h : NF (sum xs)) : Desc xs := ((nf_sum_iff xs).mp h).2.1

theorem nf_zero : NF zero := by simp [zero, nf_sum_iff, SingleOK]

/-- The elements of `E_k(α)` of a normal term are normal. -/
theorem NF.of_mem_E {k : ℕ} : ∀ {a g : ThetaWTerm}, NF a → g ∈ E k a → NF g
  | Omega _, g, _, h => by simp at h
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

/-! ### Levels occurring in a term -/

mutual
/-- `LevLT n α`: every `Ω_{k+1}` and every `ϑ_k` occurring in `α` has `k < n`. -/
def LevLT (n : ℕ) : ThetaWTerm → Prop
  | Omega k => k < n
  | theta k a => k < n ∧ LevLT n a
  | sum xs => LevLTList n xs
/-- Every entry of the list satisfies `LevLT n`. -/
def LevLTList (n : ℕ) : List ThetaWTerm → Prop
  | [] => True
  | x :: xs => LevLT n x ∧ LevLTList n xs
end

@[simp] theorem levLT_Omega (n k : ℕ) : LevLT n (Omega k) ↔ k < n := by simp [LevLT]

@[simp] theorem levLT_theta (n k : ℕ) (a : ThetaWTerm) :
    LevLT n (theta k a) ↔ k < n ∧ LevLT n a := by simp [LevLT]

theorem levLTList_iff {n : ℕ} {xs : List ThetaWTerm} :
    LevLTList n xs ↔ ∀ x ∈ xs, LevLT n x := by
  induction xs with
  | nil => simp [LevLTList]
  | cons y ys ih => simp [LevLTList, ih]

theorem levLT_sum_iff (n : ℕ) (xs : List ThetaWTerm) :
    LevLT n (sum xs) ↔ ∀ x ∈ xs, LevLT n x := by
  simp only [LevLT, levLTList_iff]

/-- The elements of `E_k(α)` inherit the level bound. -/
theorem LevLT.of_mem_E {n k : ℕ} : ∀ {a g : ThetaWTerm}, LevLT n a → g ∈ E k a → LevLT n g
  | Omega _, g, _, h => by simp at h
  | theta j a, g, ha, h => by
    by_cases hj : j ≤ k
    · rw [E_theta_of_le hj] at h; simp at h; exact h ▸ ha
    · rw [E_theta_of_lt (Nat.lt_of_not_le hj)] at h
      exact LevLT.of_mem_E ((levLT_theta n j a).mp ha).2 h
  | sum xs, g, ha, h => by
    obtain ⟨x, hx, hg⟩ := mem_E_sum.mp h
    exact LevLT.of_mem_E ((levLT_sum_iff n xs).mp ha x hx) hg
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hx

end ThetaWTerm

end OrdinalAnalysis
