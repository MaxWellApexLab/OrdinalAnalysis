/-
  Exponent lists of the multi-level ϑ-notation.

  As in the one-level system (Freund, arXiv:2204.09321, Definition 3.1), a term
  `⟨α₀, …, α_{n-1}⟩` denotes `ω^α₀ + ⋯ + ω^α_{n-1}` and the principal terms `Ω_{k+1}` and
  `ϑ_k β` denote ε-numbers, so `ω^P = P`.  Every normal term is determined by its list of
  Cantor exponents (`toList`): a principal term `P` has the single exponent `P`, and a sum
  has its entries.  Conversely every non-increasing list of normal terms is the exponent
  list of exactly one normal term (`ofList`).  Under this correspondence the order is the
  lexicographic order of the exponent lists (`ofList_lt_ofList`).  The coefficient sets and
  the level bound of `ofList xs` are the unions over the entries.
-/
import OrdinalAnalysis.Ordinal.ThetaW.Order

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

/-- The list of Cantor exponents of a term. -/
def toList : ThetaWTerm → List ThetaWTerm
  | Omega k => [Omega k]
  | theta k a => [theta k a]
  | sum xs => xs

/-- The term with a given list of Cantor exponents: a single principal exponent `P` gives
`ω^P = P`, every other list gives the sum. -/
def ofList : List ThetaWTerm → ThetaWTerm
  | [] => sum []
  | [x] => if IsPrin x then x else sum [x]
  | x :: y :: ys => sum (x :: y :: ys)

@[simp] theorem toList_sum (xs : List ThetaWTerm) : toList (sum xs) = xs := rfl

@[simp] theorem ofList_nil : ofList [] = sum [] := rfl

theorem ofList_singleton_prin {x : ThetaWTerm} (h : IsPrin x) : ofList [x] = x := by
  simp [ofList, h]

theorem ofList_singleton_not_prin {x : ThetaWTerm} (h : ¬ IsPrin x) :
    ofList [x] = sum [x] := by
  simp [ofList, h]

theorem ofList_of_singleOK {xs : List ThetaWTerm} (h : SingleOK xs) : ofList xs = sum xs := by
  match xs, h with
  | [], _ => rfl
  | [_], h => exact ofList_singleton_not_prin h
  | _ :: _ :: _, _ => rfl

theorem toList_of_isPrin {p : ThetaWTerm} (h : IsPrin p) : toList p = [p] := by
  cases p with
  | Omega _ => rfl
  | theta _ _ => rfl
  | sum _ => exact absurd h id

@[simp] theorem toList_ofList (xs : List ThetaWTerm) : toList (ofList xs) = xs := by
  match xs with
  | [] => rfl
  | [x] =>
    by_cases h : IsPrin x
    · rw [ofList_singleton_prin h, toList_of_isPrin h]
    · rw [ofList_singleton_not_prin h]; rfl
  | _ :: _ :: _ => rfl

theorem ofList_toList {t : ThetaWTerm} (h : NF t) : ofList (toList t) = t := by
  cases t with
  | Omega _ => exact ofList_singleton_prin trivial
  | theta _ _ => exact ofList_singleton_prin trivial
  | sum xs => exact ofList_of_singleOK ((nf_sum_iff xs).mp h).2.2

/-- A principal term against a sum, compared as one-entry sums. -/
theorem prin_lt_sum_iff {p : ThetaWTerm} (hp : IsPrin p) {ys : List ThetaWTerm}
    (hys : SingleOK ys) : p < sum ys ↔ sum [p] < sum ys := by
  match ys, hys with
  | [], _ => exact ⟨fun h => absurd h (not_prin_lt_nil hp), fun h => absurd h (not_lt_nil _)⟩
  | [y], hy =>
    rw [prin_lt_cons_iff hp, cons_lt_cons_iff]
    have hne : p ≠ y := fun e => hy (e ▸ hp)
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact absurd h hne
    · rintro (h | ⟨_, h⟩)
      · exact Or.inl h
      · exact absurd h not_nil_lt_nil
  | y :: z :: zs, _ =>
    rw [prin_lt_cons_iff hp, cons_lt_cons_iff]
    constructor
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, nil_lt_cons _ _⟩
    · rintro (h | ⟨rfl, _⟩)
      · exact Or.inl h
      · exact le_refl' _

/-- A sum against a principal term, compared as one-entry sums. -/
theorem sum_lt_prin_iff' {p : ThetaWTerm} (hp : IsPrin p) {xs : List ThetaWTerm} :
    sum xs < p ↔ sum xs < sum [p] := by
  cases xs with
  | nil => exact ⟨fun _ => nil_lt_cons _ _, fun _ => nil_lt_prin hp⟩
  | cons x xs =>
    rw [cons_lt_prin_iff hp, cons_lt_cons_iff]
    constructor
    · exact fun h => Or.inl h
    · rintro (h | ⟨_, h⟩)
      · exact h
      · exact absurd h (not_lt_nil _)

theorem eq_singleton_of_not_singleOK {xs : List ThetaWTerm} (h : ¬ SingleOK xs) :
    ∃ p, IsPrin p ∧ xs = [p] := by
  match xs, h with
  | [], h => exact absurd trivial h
  | [p], h => exact ⟨p, not_not.mp h, rfl⟩
  | _ :: _ :: _, h => exact absurd trivial h

/-- The order on normal terms is the order on their exponent lists. -/
theorem ofList_lt_ofList {xs ys : List ThetaWTerm} :
    ofList xs < ofList ys ↔ sum xs < sum ys := by
  by_cases hx : SingleOK xs <;> by_cases hy : SingleOK ys
  · rw [ofList_of_singleOK hx, ofList_of_singleOK hy]
  · obtain ⟨q, hq, rfl⟩ := eq_singleton_of_not_singleOK hy
    rw [ofList_of_singleOK hx, ofList_singleton_prin hq]
    exact sum_lt_prin_iff' hq
  · obtain ⟨p, hp, rfl⟩ := eq_singleton_of_not_singleOK hx
    rw [ofList_of_singleOK hy, ofList_singleton_prin hp]
    exact prin_lt_sum_iff hp hy
  · obtain ⟨q, hq, rfl⟩ := eq_singleton_of_not_singleOK hy
    obtain ⟨p, hp, rfl⟩ := eq_singleton_of_not_singleOK hx
    rw [ofList_singleton_prin hp, ofList_singleton_prin hq, cons_lt_cons_iff]
    constructor
    · exact fun h => Or.inl h
    · rintro (h | ⟨_, h⟩)
      · exact h
      · exact absurd h not_nil_lt_nil

/-- `Desc` in pairwise form. -/
theorem desc_iff_pairwise {xs : List ThetaWTerm} :
    Desc xs ↔ xs.Pairwise (fun x y => y ≤ x) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.pairwise_cons]
    constructor
    · intro h
      exact ⟨fun y hy => h.le_head y (List.mem_cons_of_mem x hy), ih.mp h.tail⟩
    · rintro ⟨h1, h2⟩
      cases xs with
      | nil => trivial
      | cons y ys => exact ⟨h1 y List.mem_cons_self, ih.mpr h2⟩

/-- The exponent lists of normal terms: non-increasing lists of normal terms. -/
def CNF (xs : List ThetaWTerm) : Prop := (∀ x ∈ xs, NF x) ∧ xs.Pairwise (fun x y => y ≤ x)

theorem nf_ofList_iff {xs : List ThetaWTerm} : NF (ofList xs) ↔ CNF xs := by
  unfold CNF
  rw [← desc_iff_pairwise]
  match xs with
  | [] => simp [nf_sum_iff, SingleOK]
  | [x] =>
    by_cases h : IsPrin x
    · rw [ofList_singleton_prin h]; simp
    · rw [ofList_singleton_not_prin h, nf_sum_iff]; simp [SingleOK, h]
  | x :: y :: ys =>
    show NF (sum (x :: y :: ys)) ↔ _
    rw [nf_sum_iff]
    simp [SingleOK]

theorem NF.cnf_toList {t : ThetaWTerm} (h : NF t) : CNF (toList t) := by
  rw [← nf_ofList_iff, ofList_toList h]; exact h

theorem CNF.tail {x : ThetaWTerm} {xs : List ThetaWTerm} (h : CNF (x :: xs)) : CNF xs :=
  ⟨fun e he => h.1 e (List.mem_cons_of_mem x he), h.2.of_cons⟩

theorem CNF.le_head {x : ThetaWTerm} {xs : List ThetaWTerm} (h : CNF (x :: xs)) :
    ∀ e ∈ x :: xs, e ≤ x := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact le_refl' _
  · exact List.rel_of_pairwise_cons h.2 he

/-- The coefficient sets of `ofList xs` are the unions over the entries. -/
theorem mem_E_ofList {k : ℕ} {g : ThetaWTerm} {xs : List ThetaWTerm} :
    g ∈ E k (ofList xs) ↔ ∃ x ∈ xs, g ∈ E k x := by
  match xs with
  | [] => simp
  | [x] =>
    by_cases h : IsPrin x
    · rw [ofList_singleton_prin h]; simp
    · rw [ofList_singleton_not_prin h]; exact mem_E_sum
  | _ :: _ :: _ => exact mem_E_sum

/-- The level bound of `ofList xs` is the conjunction over the entries. -/
theorem levLT_ofList_iff {n : ℕ} {xs : List ThetaWTerm} :
    LevLT n (ofList xs) ↔ ∀ x ∈ xs, LevLT n x := by
  match xs with
  | [] => simp [levLT_sum_iff]
  | [x] =>
    by_cases h : IsPrin x
    · rw [ofList_singleton_prin h]; simp
    · rw [ofList_singleton_not_prin h]; exact levLT_sum_iff n [x]
  | _ :: _ :: _ => exact levLT_sum_iff n _

end ThetaWTerm

end OrdinalAnalysis
