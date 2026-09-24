/-
  Arithmetic on the ϑ-notation.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Definition 3.1 and §5.  A term `⟨α₀, …, α_{n-1}⟩`
  denotes the Cantor sum `ω^α₀ + ⋯ + ω^α_{n-1}`, and the principal terms `Ω` and `ϑ β`
  denote ε-numbers, so that `ω^Ω = Ω` and `ω^{ϑ β} = ϑ β`; this is why a one-entry sum
  `⟨α₀⟩` with `α₀` principal is excluded from the normal form.

  Every normal term is therefore determined by its list of Cantor exponents (`toList`):
  `Ω` and `ϑ β` have the single exponent `Ω`, resp. `ϑ β`, and `⟨α₀, …, α_{n-1}⟩` has the
  exponents `α₀, …, α_{n-1}`.  Conversely every non-increasing list of normal terms is the
  list of exponents of exactly one normal term (`ofList`).  Under this correspondence the
  order of Definition 3.1 is the lexicographic order of the exponent lists
  (`ofList_lt_ofList`), and the arithmetic operations become list operations:

  * `ω^α` has the single exponent `α`; so `ω^α = α` for principal `α`;
  * the natural (Hessenberg) sum `α ⊕ β` merges the two non-increasing exponent lists;
  * the ordinal sum `α + β` keeps the exponents of `α` that are `≽` the first exponent
    of `β` and appends the exponents of `β`;
  * the numeral `n` is `⟨0, …, 0⟩` (`n` entries), and `1 = ω^0 = ⟨0⟩`;
  * `ω · α` replaces every exponent `α_i` by `1 + α_i` (Freund §5: `ω · Ω = Ω`,
    `ω · ϑ β = ϑ β`, `ω · ⟨α_i⟩ = ⟨1 + α_i⟩`).

  The laws are proved syntactically, from the order of Definition 3.1 alone.
-/
import OrdinalAnalysis.Ordinal.Theta.Order

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaTerm

/-! ### The exponent lists -/

/-- The list of Cantor exponents of a term: `Ω = ω^Ω` and `ϑ β = ω^{ϑ β}` have one exponent,
and `⟨α₀, …, α_{n-1}⟩` has the exponents `α₀, …, α_{n-1}`. -/
def toList : ThetaTerm → List ThetaTerm
  | Omega => [Omega]
  | theta a => [theta a]
  | sum xs => xs

/-- The term with a given list of Cantor exponents: a single principal exponent `P` gives
`ω^P = P`, every other list gives the sum. -/
def ofList : List ThetaTerm → ThetaTerm
  | [] => sum []
  | [x] => if IsPrin x then x else sum [x]
  | x :: y :: ys => sum (x :: y :: ys)

@[simp] theorem toList_Omega : toList Omega = [Omega] := rfl
@[simp] theorem toList_theta (a : ThetaTerm) : toList (theta a) = [theta a] := rfl
@[simp] theorem toList_sum (xs : List ThetaTerm) : toList (sum xs) = xs := rfl

@[simp] theorem ofList_nil : ofList [] = sum [] := rfl

theorem ofList_singleton_prin {x : ThetaTerm} (h : IsPrin x) : ofList [x] = x := by
  simp [ofList, h]

theorem ofList_singleton_not_prin {x : ThetaTerm} (h : ¬ IsPrin x) :
    ofList [x] = sum [x] := by
  simp [ofList, h]

theorem ofList_of_singleOK {xs : List ThetaTerm} (h : SingleOK xs) : ofList xs = sum xs := by
  match xs, h with
  | [], _ => rfl
  | [_], h => exact ofList_singleton_not_prin h
  | _ :: _ :: _, _ => rfl

theorem toList_of_isPrin {p : ThetaTerm} (h : IsPrin p) : toList p = [p] := by
  cases p with
  | Omega => rfl
  | theta _ => rfl
  | sum _ => exact absurd h id

@[simp] theorem toList_ofList (xs : List ThetaTerm) : toList (ofList xs) = xs := by
  match xs with
  | [] => rfl
  | [x] =>
    by_cases h : IsPrin x
    · rw [ofList_singleton_prin h, toList_of_isPrin h]
    · rw [ofList_singleton_not_prin h]; rfl
  | _ :: _ :: _ => rfl

theorem ofList_injective {xs ys : List ThetaTerm} (h : ofList xs = ofList ys) : xs = ys := by
  rw [← toList_ofList xs, ← toList_ofList ys, h]

theorem ofList_toList {t : ThetaTerm} (h : NF t) : ofList (toList t) = t := by
  cases t with
  | Omega => exact ofList_singleton_prin trivial
  | theta a => exact ofList_singleton_prin trivial
  | sum xs => exact ofList_of_singleOK ((nf_sum_iff xs).mp h).2.2

/-! ### The order on exponent lists

The order of Definition 3.1 restricted to the sums is the lexicographic order of the lists
(`sum_lt_sum_iff_lex`); via `ofList` it is the order of all normal terms. -/

/-- A principal term against a sum, compared as one-entry sums. -/
theorem prin_lt_sum_iff {p : ThetaTerm} (hp : IsPrin p) {ys : List ThetaTerm}
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
theorem sum_lt_prin_iff' {p : ThetaTerm} (hp : IsPrin p) {xs : List ThetaTerm} :
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

theorem eq_singleton_of_not_singleOK {xs : List ThetaTerm} (h : ¬ SingleOK xs) :
    ∃ p, IsPrin p ∧ xs = [p] := by
  match xs, h with
  | [], h => exact absurd trivial h
  | [p], h => exact ⟨p, not_not.mp h, rfl⟩
  | _ :: _ :: _, h => exact absurd trivial h

/-- The order on normal terms is the order on their exponent lists. -/
theorem ofList_lt_ofList {xs ys : List ThetaTerm} :
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

theorem ofList_le_ofList {xs ys : List ThetaTerm} :
    ofList xs ≤ ofList ys ↔ sum xs ≤ sum ys := by
  rw [le_def, le_def, ofList_lt_ofList]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (congrArg sum (ofList_injective h))
  · rintro (h | h)
    · exact Or.inl h
    · cases h; exact Or.inr rfl

/-! ### Non-increasing lists in pairwise form -/

/-- `Desc` in pairwise form: every later entry is `≼` every earlier one. -/
theorem desc_iff_pairwise {xs : List ThetaTerm} :
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
def CNF (xs : List ThetaTerm) : Prop := (∀ x ∈ xs, NF x) ∧ xs.Pairwise (fun x y => y ≤ x)

theorem nf_ofList_iff {xs : List ThetaTerm} : NF (ofList xs) ↔ CNF xs := by
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

theorem NF.cnf_toList {t : ThetaTerm} (h : NF t) : CNF (toList t) := by
  rw [← nf_ofList_iff, ofList_toList h]; exact h

theorem not_le_iff_lt {a b : ThetaTerm} (h : ¬ a ≤ b) : b < a := by
  rcases lt_trichotomy' a b with h' | rfl | h'
  · exact absurd (Or.inl h') h
  · exact absurd (le_refl' _) h
  · exact h'

/-! ### Sorted lists

A non-increasing list is determined by the multiset of its entries: two non-increasing
lists that are permutations of each other are equal, since `≼` is antisymmetric. -/

/-- Non-increasing lists, in pairwise form. -/
abbrev SortedDesc (xs : List ThetaTerm) : Prop := xs.Pairwise (fun x y => y ≤ x)

theorem CNF.sorted {xs : List ThetaTerm} (h : CNF xs) : SortedDesc xs := h.2

theorem CNF.nf {xs : List ThetaTerm} (h : CNF xs) {x : ThetaTerm} (hx : x ∈ xs) : NF x :=
  h.1 x hx

theorem eq_of_perm_of_sortedDesc {xs ys : List ThetaTerm} (hx : SortedDesc xs)
    (hy : SortedDesc ys) (h : xs.Perm ys) : xs = ys :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm' h2 h1) hx hy h

theorem SortedDesc.le_head {x : ThetaTerm} {xs : List ThetaTerm} (h : SortedDesc (x :: xs))
    {y : ThetaTerm} (hy : y ∈ xs) : y ≤ x :=
  List.rel_of_pairwise_cons h hy

/-! ### The merge of two non-increasing lists -/

/-- The comparison used by the merge: `x` goes first when `y ≼ x`. -/
def geb (x y : ThetaTerm) : Bool := decide (y ≤ x)

/-- The merge of two lists; on non-increasing lists it is the non-increasing arrangement of
the union of the two multisets of entries. -/
def mergeL (xs ys : List ThetaTerm) : List ThetaTerm := List.merge xs ys geb

theorem mergeL_perm (xs ys : List ThetaTerm) : (mergeL xs ys).Perm (xs ++ ys) :=
  List.merge_perm_append geb

@[simp] theorem mergeL_nil_left (ys : List ThetaTerm) : mergeL [] ys = ys := List.nil_merge ys

@[simp] theorem mergeL_nil_right (xs : List ThetaTerm) : mergeL xs [] = xs :=
  List.merge_right xs

theorem mem_mergeL {z : ThetaTerm} {xs ys : List ThetaTerm} :
    z ∈ mergeL xs ys ↔ z ∈ xs ∨ z ∈ ys :=
  List.mem_merge

theorem mergeL_cons_cons_of_le {x y : ThetaTerm} (xs ys : List ThetaTerm) (h : y ≤ x) :
    mergeL (x :: xs) (y :: ys) = x :: mergeL xs (y :: ys) :=
  List.cons_merge_cons_pos geb xs ys (by simp [geb, h])

theorem mergeL_cons_cons_of_lt {x y : ThetaTerm} (xs ys : List ThetaTerm) (h : x < y) :
    mergeL (x :: xs) (y :: ys) = y :: mergeL (x :: xs) ys :=
  List.cons_merge_cons_neg geb xs ys (by simp [geb, not_le_of_lt' h])

theorem sortedDesc_mergeL {xs ys : List ThetaTerm} (hx : SortedDesc xs) (hy : SortedDesc ys) :
    SortedDesc (mergeL xs ys) := by
  have h := List.pairwise_merge (le := geb)
    (fun a b c hab hbc => by
      simp only [geb, decide_eq_true_eq] at hab hbc ⊢; exact le_trans' hbc hab)
    (fun a b => by
      rcases le_total' a b with h | h <;> simp [geb, h])
    xs ys (hx.imp (fun h => by simpa [geb] using h)) (hy.imp (fun h => by simpa [geb] using h))
  exact h.imp (fun h => by simpa [geb] using h)

theorem CNF.mergeL {xs ys : List ThetaTerm} (hx : CNF xs) (hy : CNF ys) :
    CNF (mergeL xs ys) :=
  ⟨fun _ hz => (mem_mergeL.mp hz).elim hx.nf hy.nf, sortedDesc_mergeL hx.sorted hy.sorted⟩

/-- The merge is the unique non-increasing arrangement of the union. -/
theorem mergeL_eq_of_perm {xs ys zs : List ThetaTerm} (hx : SortedDesc xs) (hy : SortedDesc ys)
    (hz : SortedDesc zs) (h : zs.Perm (xs ++ ys)) : mergeL xs ys = zs :=
  eq_of_perm_of_sortedDesc (sortedDesc_mergeL hx hy) hz ((mergeL_perm xs ys).trans h.symm)

theorem mergeL_comm {xs ys : List ThetaTerm} (hx : SortedDesc xs) (hy : SortedDesc ys) :
    mergeL xs ys = mergeL ys xs :=
  mergeL_eq_of_perm hx hy (sortedDesc_mergeL hy hx)
    ((mergeL_perm ys xs).trans List.perm_append_comm)

theorem mergeL_assoc {xs ys zs : List ThetaTerm} (hx : SortedDesc xs) (hy : SortedDesc ys)
    (hz : SortedDesc zs) : mergeL (mergeL xs ys) zs = mergeL xs (mergeL ys zs) := by
  refine mergeL_eq_of_perm (sortedDesc_mergeL hx hy) hz
    (sortedDesc_mergeL hx (sortedDesc_mergeL hy hz)) ?_
  refine (mergeL_perm _ _).trans ?_
  refine (List.Perm.append_left xs (mergeL_perm ys zs)).trans ?_
  refine List.Perm.trans ?_ (List.Perm.append_right zs (mergeL_perm xs ys).symm)
  rw [List.append_assoc]

/-- Moving an entry across a merge: `x :: xs` and `ys` merge like `xs` and `x :: ys`, when
`x` may head both lists. -/
theorem mergeL_cons_left_eq {x : ThetaTerm} {xs ys : List ThetaTerm}
    (hx : SortedDesc (x :: xs)) (hy : SortedDesc (x :: ys)) :
    mergeL xs (x :: ys) = mergeL (x :: xs) ys :=
  mergeL_eq_of_perm hx.of_cons hy (sortedDesc_mergeL hx (hy.of_cons))
    ((mergeL_perm _ _).trans List.perm_middle.symm)

/-- A non-increasing list is below its merge with a non-empty list. -/
theorem lt_mergeL_right : ∀ {ys zs : List ThetaTerm}, SortedDesc ys → SortedDesc zs →
    zs ≠ [] → sum ys < sum (mergeL zs ys)
  | [], zs, _, _, hne => by
    rw [mergeL_nil_right]
    obtain ⟨z, zs', rfl⟩ := List.exists_cons_of_ne_nil hne
    exact nil_lt_cons z zs'
  | y :: ys, [], _, _, hne => absurd rfl hne
  | y :: ys, z :: zs, hy, hz, _ => by
    by_cases h : y ≤ z
    · rw [mergeL_cons_cons_of_le zs ys h, cons_lt_cons_iff]
      rcases h with h | rfl
      · exact Or.inl h
      · refine Or.inr ⟨rfl, ?_⟩
        rw [mergeL_cons_left_eq hz hy]
        exact lt_mergeL_right hy.of_cons hz (List.cons_ne_nil _ _)
    · have h' : z < y := by
        rcases lt_trichotomy' z y with h' | rfl | h'
        · exact h'
        · exact absurd (le_refl' _) h
        · exact absurd (Or.inl h') h
      rw [mergeL_cons_cons_of_lt zs ys h', cons_lt_cons_iff]
      exact Or.inr ⟨rfl, lt_mergeL_right hy.of_cons hz (List.cons_ne_nil _ _)⟩

/-- The merge is strictly monotone in its left argument. -/
theorem mergeL_lt_mergeL_left : ∀ (ys : List ThetaTerm) {xs xs' : List ThetaTerm},
    SortedDesc xs → SortedDesc xs' → SortedDesc ys → sum xs < sum xs' →
    sum (mergeL xs ys) < sum (mergeL xs' ys)
  | [], xs, xs', _, _, _, h => by simpa using h
  | y :: ys, xs, xs', hx, hx', hy, h => by
    have IH := fun {xs xs' : List ThetaTerm} => mergeL_lt_mergeL_left ys (xs := xs) (xs' := xs')
    have hlex := (sum_lt_sum_iff_lex xs xs').mp h
    clear h
    induction hlex with
    | nil =>
      rw [mergeL_nil_left]
      exact lt_mergeL_right hy hx' (List.cons_ne_nil _ _)
    | @cons a l1 l2 _ ih =>
      by_cases hya : y ≤ a
      · rw [mergeL_cons_cons_of_le _ _ hya, mergeL_cons_cons_of_le _ _ hya, cons_lt_cons_iff]
        exact Or.inr ⟨rfl, ih hx.of_cons hx'.of_cons⟩
      · have hay : a < y := not_le_iff_lt hya
        rw [mergeL_cons_cons_of_lt _ _ hay, mergeL_cons_cons_of_lt _ _ hay, cons_lt_cons_iff]
        refine Or.inr ⟨rfl, IH hx hx' hy.of_cons ?_⟩
        rw [sum_lt_sum_iff_lex]
        exact List.Lex.cons (by assumption)
    | @rel a1 l1 a2 l2 h12 =>
      have hlt : sum (a1 :: l1) < sum (a2 :: l2) := (cons_lt_cons_iff _ _ _ _).mpr (Or.inl h12)
      by_cases h1 : y ≤ a1
      · have h2 : y ≤ a2 := le_trans' h1 (Or.inl h12)
        rw [mergeL_cons_cons_of_le _ _ h1, mergeL_cons_cons_of_le _ _ h2, cons_lt_cons_iff]
        exact Or.inl h12
      · have h1' : a1 < y := not_le_iff_lt h1
        rw [mergeL_cons_cons_of_lt _ _ h1']
        by_cases h2 : y ≤ a2
        · rw [mergeL_cons_cons_of_le _ _ h2, cons_lt_cons_iff]
          rcases h2 with h2 | rfl
          · exact Or.inl h2
          · refine Or.inr ⟨rfl, ?_⟩
            rw [mergeL_cons_left_eq hx' hy]
            exact IH hx hx' hy.of_cons hlt
        · have h2' : a2 < y := not_le_iff_lt h2
          rw [mergeL_cons_cons_of_lt _ _ h2', cons_lt_cons_iff]
          exact Or.inr ⟨rfl, IH hx hx' hy.of_cons hlt⟩

/-! ### Comparing lists with a common prefix, and one-entry bounds -/

theorem sum_append_lt_sum_append (zs : List ThetaTerm) {xs ys : List ThetaTerm}
    (h : sum xs < sum ys) : sum (zs ++ xs) < sum (zs ++ ys) := by
  induction zs with
  | nil => exact h
  | cons z zs ih => exact (cons_lt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, ih⟩)

/-- A non-increasing list is below `⟨α⟩` iff all its entries are below `α`. -/
theorem sum_lt_singleton_iff {xs : List ThetaTerm} (hx : SortedDesc xs) (a : ThetaTerm) :
    sum xs < sum [a] ↔ ∀ x ∈ xs, x < a := by
  cases xs with
  | nil => simp [nil_lt_cons]
  | cons x xs =>
    rw [cons_lt_cons_iff]
    constructor
    · rintro (h | ⟨_, h⟩)
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h
        · exact lt_of_le_of_lt' (hx.le_head hy) h
      · exact absurd h (not_lt_nil _)
    · intro h
      exact Or.inl (h x List.mem_cons_self)

/-- A list whose entries are all below `β₀` is below `⟨β₀, …⟩`. -/
theorem sum_lt_cons_of_forall_lt {xs : List ThetaTerm} {b : ThetaTerm} (bs : List ThetaTerm)
    (h : ∀ x ∈ xs, x < b) : sum xs < sum (b :: bs) := by
  cases xs with
  | nil => exact nil_lt_cons b bs
  | cons x xs => exact (cons_lt_cons_iff _ _ _ _).mpr (Or.inl (h x List.mem_cons_self))

/-! ### The ordinal sum of exponent lists

`ω^α₀ + ⋯ + ω^α_{m-1} + ω^β₀ + ⋯ = ω^α₀ + ⋯ + ω^α_{k-1} + ω^β₀ + ⋯`, where `α_{k-1}` is the
last exponent `≽ β₀`: the summands `ω^α_i` with `α_i ≺ β₀` are absorbed by `ω^β₀`. -/

/-- The exponent list of `α + β`. -/
def addL (xs : List ThetaTerm) : List ThetaTerm → List ThetaTerm
  | [] => xs
  | y :: ys => xs.filter (fun x => geb x y) ++ y :: ys

@[simp] theorem addL_nil (xs : List ThetaTerm) : addL xs [] = xs := rfl

theorem addL_cons (xs : List ThetaTerm) (y : ThetaTerm) (ys : List ThetaTerm) :
    addL xs (y :: ys) = xs.filter (fun x => geb x y) ++ y :: ys := rfl

@[simp] theorem nil_addL (ys : List ThetaTerm) : addL [] ys = ys := by
  cases ys <;> rfl

theorem mem_filter_geb {x y : ThetaTerm} {xs : List ThetaTerm} :
    x ∈ xs.filter (fun x => geb x y) ↔ x ∈ xs ∧ y ≤ x := by
  simp [geb]

theorem mem_addL {z : ThetaTerm} {xs ys : List ThetaTerm} (h : z ∈ addL xs ys) :
    z ∈ xs ∨ z ∈ ys := by
  cases ys with
  | nil => exact Or.inl h
  | cons y ys =>
    rcases List.mem_append.mp h with h | h
    · exact Or.inl (mem_filter_geb.mp h).1
    · exact Or.inr h

theorem sortedDesc_addL {xs ys : List ThetaTerm} (hx : SortedDesc xs) (hy : SortedDesc ys) :
    SortedDesc (addL xs ys) := by
  cases ys with
  | nil => exact hx
  | cons y ys =>
    rw [addL_cons]
    unfold SortedDesc
    rw [List.pairwise_append]
    refine ⟨hx.filter _, hy, fun a ha b hb => ?_⟩
    have hya := (mem_filter_geb.mp ha).2
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hya
    · exact le_trans' (hy.le_head hb) hya

theorem CNF.addL {xs ys : List ThetaTerm} (hx : CNF xs) (hy : CNF ys) : CNF (addL xs ys) :=
  ⟨fun _ hz => (mem_addL hz).elim hx.nf hy.nf, sortedDesc_addL hx.sorted hy.sorted⟩

/-- Associativity of the ordinal sum, on exponent lists. -/
theorem addL_assoc (xs : List ThetaTerm) {ys : List ThetaTerm} (hy : SortedDesc ys)
    (zs : List ThetaTerm) : addL (addL xs ys) zs = addL xs (addL ys zs) := by
  cases zs with
  | nil => rfl
  | cons z zs =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      rw [addL_cons, addL_cons, addL_cons, List.filter_append]
      by_cases hzy : z ≤ y
      · rw [List.filter_cons_of_pos (by simp [geb, hzy]), List.cons_append, addL_cons]
        simp only [List.cons_append, List.append_assoc]
        congr 1
        rw [List.filter_eq_self]
        intro x hx
        simp only [geb, decide_eq_true_eq] at hx ⊢
        exact le_trans' hzy (mem_filter_geb.mp hx).2
      · have hyz : y < z := not_le_iff_lt hzy
        have hnil : (y :: ys).filter (fun x => geb x z) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          simp only [geb, decide_eq_true_eq]
          intro hzx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hzy hzx
          · exact hzy (le_trans' hzx (hy.le_head hx))
        rw [hnil, List.nil_append, List.append_nil, addL_cons, List.filter_filter]
        congr 1
        apply List.filter_congr
        intro x _
        simp only [geb]
        by_cases hzx : z ≤ x
        · simp [hzx, le_trans' (Or.inl hyz) hzx]
        · simp [hzx]

/-- A non-increasing list splits into its entries `≽ t` followed by entries `≺ t`. -/
theorem exists_filter_append {xs : List ThetaTerm} (hx : SortedDesc xs) (t : ThetaTerm) :
    ∃ S, xs = xs.filter (fun x => geb x t) ++ S ∧ ∀ s ∈ S, s < t := by
  induction xs with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons x xs ih =>
    by_cases htx : t ≤ x
    · obtain ⟨S, hS, hlt⟩ := ih hx.of_cons
      refine ⟨S, ?_, hlt⟩
      rw [List.filter_cons_of_pos (by simp [geb, htx]), List.cons_append, ← hS]
    · have hxt : x < t := not_le_iff_lt htx
      refine ⟨x :: xs, ?_, ?_⟩
      · rw [List.filter_eq_nil_iff.mpr, List.nil_append]
        intro y hy
        simp only [geb, decide_eq_true_eq]
        intro hty
        rcases List.mem_cons.mp hy with rfl | hy
        · exact htx hty
        · exact htx (le_trans' hty (hx.le_head hy))
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hxt
        · exact lt_of_le_of_lt' (hx.le_head hs) hxt

/-- The ordinal sum is strictly monotone in its right argument. -/
theorem addL_lt_addL_right {xs ys ys' : List ThetaTerm} (hx : SortedDesc xs)
    (h : sum ys < sum ys') : sum (addL xs ys) < sum (addL xs ys') := by
  cases ys' with
  | nil => exact absurd h (not_lt_nil _)
  | cons y' ys' =>
    obtain ⟨S, hS, hlt⟩ := exists_filter_append hx y'
    cases ys with
    | nil =>
      rw [addL_nil, addL_cons]
      conv_lhs => rw [hS]
      exact sum_append_lt_sum_append _ (sum_lt_cons_of_forall_lt ys' hlt)
    | cons y ys =>
      rw [addL_cons, addL_cons]
      rcases (cons_lt_cons_iff _ _ _ _).mp h with h | ⟨rfl, h2⟩
      · have hF : xs.filter (fun x => geb x y) =
            xs.filter (fun x => geb x y') ++ S.filter (fun x => geb x y) := by
          conv_lhs => rw [hS]
          rw [List.filter_append]
          congr 1
          rw [List.filter_eq_self]
          intro x hx'
          simp only [geb, decide_eq_true_eq]
          exact le_trans' (Or.inl h) (mem_filter_geb.mp hx').2
        rw [hF, List.append_assoc]
        refine sum_append_lt_sum_append _ ?_
        cases hSf : S.filter (fun x => geb x y) with
        | nil => exact (cons_lt_cons_iff _ _ _ _).mpr (Or.inl h)
        | cons s S' =>
          have hs : s ∈ S := (mem_filter_geb.mp (hSf ▸ List.mem_cons_self)).1
          exact (cons_lt_cons_iff _ _ _ _).mpr (Or.inl (hlt s hs))
      · exact sum_append_lt_sum_append _ ((cons_lt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, h2⟩))

/-- Adding a least entry `0` at the end: `xs` merged with `⟨0⟩` is `xs` followed by `0`. -/
theorem mergeL_nil_singleton {xs : List ThetaTerm} (hx : SortedDesc xs) :
    mergeL xs [sum []] = xs ++ [sum []] := by
  refine mergeL_eq_of_perm hx (List.pairwise_singleton _ _) ?_ (List.Perm.refl _)
  unfold SortedDesc
  rw [List.pairwise_append]
  refine ⟨hx, List.pairwise_singleton _ _, fun a _ b hb => ?_⟩
  rw [List.mem_singleton.mp hb]
  exact nil_le a

/-- `α + 1` on exponent lists: `xs` followed by `0`. -/
theorem addL_nil_singleton (xs : List ThetaTerm) : addL xs [sum []] = xs ++ [sum []] := by
  rw [addL_cons, List.filter_eq_self.mpr]
  intro x _
  simp [geb, nil_le x]

/-- If every entry of `xs` is below `a`, then `xs` is absorbed: `α + ω^a = ω^a`. -/
theorem addL_singleton_of_forall_lt {xs : List ThetaTerm} {a : ThetaTerm}
    (h : ∀ x ∈ xs, x < a) : addL xs [a] = [a] := by
  rw [addL_cons, List.filter_eq_nil_iff.mpr, List.nil_append]
  intro x hx
  simp only [geb, decide_eq_true_eq]
  exact not_le_of_lt' (h x hx)

/-! ### `1 + α` on terms, for `ω · α` -/

/-- The term `1 + α`. -/
def onePlus (e : ThetaTerm) : ThetaTerm := ofList (addL [sum []] (toList e))

theorem NF.onePlus {e : ThetaTerm} (h : NF e) : NF (onePlus e) :=
  nf_ofList_iff.mpr (CNF.addL ⟨by simp [nf_zero'], List.pairwise_singleton _ _⟩ h.cnf_toList)
where nf_zero' : NF (sum []) := nf_zero

theorem onePlus_lt_onePlus {e e' : ThetaTerm} (he : NF e) (he' : NF e') (h : e < e') :
    onePlus e < onePlus e' := by
  unfold onePlus
  rw [ofList_lt_ofList]
  refine addL_lt_addL_right (List.pairwise_singleton _ _) ?_
  rwa [← ofList_lt_ofList, ofList_toList he, ofList_toList he']

theorem onePlus_le_onePlus {e e' : ThetaTerm} (he : NF e) (he' : NF e') (h : e ≤ e') :
    onePlus e ≤ onePlus e' := by
  rcases h with h | rfl
  · exact Or.inl (onePlus_lt_onePlus he he' h)
  · exact le_refl' _

/-- `1 + P = P` for principal `P`. -/
theorem onePlus_of_isPrin {p : ThetaTerm} (hp : IsPrin p) : onePlus p = p := by
  unfold onePlus
  rw [toList_of_isPrin hp, addL_cons, List.filter_eq_nil_iff.mpr, List.nil_append,
    ofList_singleton_prin hp]
  intro x hx
  rw [List.mem_singleton.mp hx]
  simp only [geb, decide_eq_true_eq]
  rintro (h | h)
  · exact not_prin_lt_nil hp h
  · cases p with
    | Omega => cases h
    | theta _ => cases h
    | sum _ => exact hp

/-- A strictly monotone map on normal entries preserves the order of exponent lists. -/
theorem sum_map_lt_sum_map {f : ThetaTerm → ThetaTerm}
    (hf : ∀ {x y : ThetaTerm}, NF x → NF y → x < y → f x < f y) :
    ∀ {xs ys : List ThetaTerm}, (∀ x ∈ xs, NF x) → (∀ y ∈ ys, NF y) → sum xs < sum ys →
      sum (xs.map f) < sum (ys.map f) := by
  intro xs ys hx hy h
  rw [sum_lt_sum_iff_lex] at h
  induction h with
  | nil => exact nil_lt_cons _ _
  | rel h =>
    simp only [List.map_cons]
    exact (cons_lt_cons_iff _ _ _ _).mpr
      (Or.inl (hf (hx _ List.mem_cons_self) (hy _ List.mem_cons_self) h))
  | cons _ ih =>
    simp only [List.map_cons]
    exact (cons_lt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl,
      ih (fun x hx' => hx x (List.mem_cons_of_mem _ hx'))
        (fun y hy' => hy y (List.mem_cons_of_mem _ hy'))⟩)

end ThetaTerm

/-! ### The operations on normal forms -/

namespace ThetaNote

open ThetaTerm

/-- The Cantor exponents of a normal form. -/
def entries (a : ThetaNote) : List ThetaTerm := toList a.1

theorem cnf_entries (a : ThetaNote) : CNF a.entries := NF.cnf_toList a.2

theorem sorted_entries (a : ThetaNote) : SortedDesc a.entries := (cnf_entries a).sorted

/-- The normal form with a given non-increasing list of normal exponents. -/
def ofEntries (xs : List ThetaTerm) (h : CNF xs) : ThetaNote := ⟨ofList xs, nf_ofList_iff.mpr h⟩

@[simp] theorem entries_ofEntries (xs : List ThetaTerm) (h : CNF xs) :
    (ofEntries xs h).entries = xs :=
  toList_ofList xs

theorem ext_entries {a b : ThetaNote} (h : a.entries = b.entries) : a = b := by
  apply Subtype.ext
  calc a.1 = ofList (toList a.1) := (ofList_toList a.2).symm
    _ = ofList (toList b.1) := congrArg ofList h
    _ = b.1 := ofList_toList b.2

/-- The order of normal forms is the lexicographic order of their exponent lists. -/
theorem lt_iff_entries {a b : ThetaNote} : a < b ↔ sum a.entries < sum b.entries := by
  show a.1 < b.1 ↔ _
  unfold entries
  rw [← ofList_lt_ofList, ofList_toList a.2, ofList_toList b.2]

theorem le_iff_entries {a b : ThetaNote} : a ≤ b ↔ sum a.entries ≤ sum b.entries := by
  show a.1 ≤ b.1 ↔ _
  unfold entries
  rw [← ofList_le_ofList, ofList_toList a.2, ofList_toList b.2]

@[simp] theorem entries_zero : zero.entries = [] := rfl

@[simp] theorem entries_Omega : Omega.entries = [ThetaTerm.Omega] := rfl

@[simp] theorem entries_theta (b : ThetaNote) : (theta b).entries = [ThetaTerm.theta b.1] := rfl

/-! #### The natural sum -/

/-- The natural (Hessenberg) sum: the merge of the exponent lists. -/
def nadd (a b : ThetaNote) : ThetaNote :=
  ofEntries (mergeL a.entries b.entries) ((cnf_entries a).mergeL (cnf_entries b))

@[simp] theorem entries_nadd (a b : ThetaNote) :
    (ThetaNote.nadd a b).entries = mergeL a.entries b.entries :=
  entries_ofEntries _ _

theorem nadd_comm (a b : ThetaNote) : ThetaNote.nadd a b = ThetaNote.nadd b a :=
  ext_entries (by simp only [entries_nadd]; exact mergeL_comm (sorted_entries a) (sorted_entries b))

theorem nadd_assoc (a b c : ThetaNote) :
    ThetaNote.nadd (ThetaNote.nadd a b) c = ThetaNote.nadd a (ThetaNote.nadd b c) :=
  ext_entries (by
    simp only [entries_nadd]
    exact mergeL_assoc (sorted_entries a) (sorted_entries b) (sorted_entries c))

theorem nadd_zero (a : ThetaNote) : ThetaNote.nadd a zero = a :=
  ext_entries (by simp)

theorem zero_nadd (a : ThetaNote) : ThetaNote.nadd zero a = a :=
  ext_entries (by simp)

theorem nadd_lt_nadd_left {a a' : ThetaNote} (b : ThetaNote) (h : a < a') :
    ThetaNote.nadd a b < ThetaNote.nadd a' b := by
  rw [lt_iff_entries, entries_nadd, entries_nadd]
  exact mergeL_lt_mergeL_left _ (sorted_entries a) (sorted_entries a') (sorted_entries b)
    (lt_iff_entries.mp h)

theorem nadd_lt_nadd_right (a : ThetaNote) {b b' : ThetaNote} (h : b < b') :
    ThetaNote.nadd a b < ThetaNote.nadd a b' := by
  rw [nadd_comm a b, nadd_comm a b']
  exact nadd_lt_nadd_left a h

theorem nadd_le_nadd_right (a : ThetaNote) {b b' : ThetaNote} (h : b ≤ b') :
    ThetaNote.nadd a b ≤ ThetaNote.nadd a b' := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (nadd_lt_nadd_right a h)
  · exact le_rfl

theorem le_nadd_left (a b : ThetaNote) : a ≤ ThetaNote.nadd a b := by
  have h := nadd_le_nadd_right a (bot_le : (⊥ : ThetaNote) ≤ b)
  rwa [bot_eq_zero, nadd_zero] at h

theorem le_nadd_right (a b : ThetaNote) : b ≤ ThetaNote.nadd a b := by
  rw [nadd_comm]; exact le_nadd_left b a

/-! #### `ω^·` -/

/-- `ω^α`: the normal form with the single exponent `α`.  For principal `α` this is `α`
itself (`ω^Ω = Ω`, `ω^{ϑ β} = ϑ β`), otherwise it is the sum `⟨α⟩`. -/
def omegaPow (a : ThetaNote) : ThetaNote :=
  ofEntries [a.1] ⟨by simpa using a.2, List.pairwise_singleton _ _⟩

@[simp] theorem entries_omegaPow (a : ThetaNote) : (omegaPow a).entries = [a.1] :=
  entries_ofEntries _ _

theorem omegaPow_lt_omegaPow {a b : ThetaNote} (h : a < b) : omegaPow a < omegaPow b := by
  rw [lt_iff_entries, entries_omegaPow, entries_omegaPow]
  exact (cons_lt_cons_iff _ _ _ _).mpr (Or.inl h)

theorem omegaPow_le_omegaPow {a b : ThetaNote} (h : a ≤ b) : omegaPow a ≤ omegaPow b := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (omegaPow_lt_omegaPow h)
  · exact le_rfl

theorem omegaPow_lt_omegaPow_iff {a b : ThetaNote} : omegaPow a < omegaPow b ↔ a < b :=
  ⟨fun h => lt_of_not_ge fun h' => absurd h (not_lt_of_ge (omegaPow_le_omegaPow h')),
    omegaPow_lt_omegaPow⟩

theorem omegaPow_injective {a b : ThetaNote} (h : omegaPow a = omegaPow b) : a = b := by
  have := congrArg entries h
  simp only [entries_omegaPow, List.cons.injEq, and_true] at this
  exact Subtype.ext this

/-- Below `ω^α` are exactly the normal forms all of whose exponents are below `α`. -/
theorem lt_omegaPow_iff {x a : ThetaNote} : x < omegaPow a ↔ ∀ e ∈ x.entries, e < a.1 := by
  rw [lt_iff_entries, entries_omegaPow]
  exact sum_lt_singleton_iff (sorted_entries x) a.1

/-- `ω^α` is additively indecomposable for the natural sum. -/
theorem nadd_lt_omegaPow {a x y : ThetaNote} (hx : x < omegaPow a) (hy : y < omegaPow a) :
    ThetaNote.nadd x y < omegaPow a := by
  rw [lt_omegaPow_iff] at hx hy ⊢
  intro e he
  rw [entries_nadd] at he
  exact (mem_mergeL.mp he).elim (hx e) (hy e)

/-! #### `1`, the numerals and the successor -/

/-- `1 = ω^0 = ⟨0⟩`. -/
def one : ThetaNote := omegaPow zero

theorem one_eq_omegaPow_zero : one = omegaPow zero := rfl

@[simp] theorem entries_one : one.entries = [sum []] := rfl

theorem one_le_omegaPow (a : ThetaNote) : one ≤ omegaPow a :=
  omegaPow_le_omegaPow (bot_le : (⊥ : ThetaNote) ≤ a)

theorem zero_lt_one : zero < one := by
  rw [lt_iff_entries]; exact nil_lt_cons _ _

/-- The numeral `n = ⟨0, …, 0⟩` (`n` entries). -/
def ofNat (n : ℕ) : ThetaNote :=
  ofEntries (List.replicate n (sum []))
    ⟨fun x hx => by rw [List.eq_of_mem_replicate hx]; exact nf_zero,
      List.pairwise_replicate.mpr (Or.inr (le_refl' _))⟩

@[simp] theorem entries_ofNat (n : ℕ) : (ofNat n).entries = List.replicate n (sum []) :=
  entries_ofEntries _ _

theorem ofNat_zero : ofNat 0 = zero := ext_entries (by simp)

theorem ofNat_one : ofNat 1 = one := ext_entries (by simp)

theorem ofNat_lt_ofNat {m n : ℕ} (h : m < n) : ofNat m < ofNat n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [lt_iff_entries, entries_ofNat, entries_ofNat, show m + k + 1 = m + (k + 1) by omega,
    List.replicate_add, List.replicate_succ]
  exact sum_lt_sum_append _ _ _

theorem entries_nadd_one (a : ThetaNote) :
    (ThetaNote.nadd a one).entries = a.entries ++ [sum []] := by
  rw [entries_nadd, entries_one, mergeL_nil_singleton (sorted_entries a)]

theorem lt_nadd_one (a : ThetaNote) : a < ThetaNote.nadd a one := by
  rw [lt_iff_entries, entries_nadd_one]
  exact sum_lt_sum_append _ _ _

/-- The successor `α + 1`, as `α ⊕ 1`. -/
def succ (a : ThetaNote) : ThetaNote := ThetaNote.nadd a one

theorem lt_succ (a : ThetaNote) : a < succ a := lt_nadd_one a

theorem ofNat_succ (n : ℕ) : ofNat (n + 1) = succ (ofNat n) :=
  ext_entries (by rw [succ, entries_nadd_one, entries_ofNat, entries_ofNat, List.replicate_succ'])

/-! #### The ordinal sum -/

/-- The ordinal sum `α + β`. -/
def add (a b : ThetaNote) : ThetaNote :=
  ofEntries (addL a.entries b.entries) ((cnf_entries a).addL (cnf_entries b))

instance : Add ThetaNote := ⟨add⟩

theorem add_def (a b : ThetaNote) : a + b = add a b := rfl

@[simp] theorem entries_add (a b : ThetaNote) :
    (a + b).entries = addL a.entries b.entries :=
  entries_ofEntries _ ((cnf_entries a).addL (cnf_entries b))

/-- The ordinal sum is associative. -/
theorem add_assoc (a b c : ThetaNote) : a + b + c = a + (b + c) :=
  ext_entries (by simp only [entries_add]; exact addL_assoc _ (sorted_entries b) _)

theorem add_zero (a : ThetaNote) : a + zero = a := ext_entries (by simp)

theorem zero_add (a : ThetaNote) : zero + a = a := ext_entries (by simp)

/-- The ordinal sum is strictly monotone in its right argument. -/
theorem add_lt_add_left (a : ThetaNote) {b c : ThetaNote} (h : b < c) : a + b < a + c := by
  rw [lt_iff_entries, entries_add, entries_add]
  exact addL_lt_addL_right (sorted_entries a) (lt_iff_entries.mp h)

theorem add_le_add_left (a : ThetaNote) {b c : ThetaNote} (h : b ≤ c) : a + b ≤ a + c := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (add_lt_add_left a h)
  · exact le_rfl

theorem le_add_left (a b : ThetaNote) : b ≤ a + b := by
  rw [le_iff_entries, entries_add]
  cases hb : b.entries with
  | nil => exact nil_le _
  | cons y ys =>
    have hs : SortedDesc (addL a.entries (y :: ys)) :=
      sortedDesc_addL (sorted_entries a) (hb ▸ sorted_entries b)
    rw [addL_cons] at hs ⊢
    exact sum_le_sum_of_forall₂ (List.forall₂_same.mpr fun x _ => le_refl' x)
      (desc_iff_pairwise.mpr hs) (List.sublist_append_right _ _).subperm

theorem add_one_eq_succ (a : ThetaNote) : a + one = succ a :=
  ext_entries (by rw [succ, entries_nadd_one, entries_add, entries_one, addL_nil_singleton])

/-- `α + ω^β = ω^β` whenever `α ≺ ω^β`. -/
theorem add_omegaPow_of_lt {x a : ThetaNote} (h : x < omegaPow a) : x + omegaPow a = omegaPow a :=
  ext_entries (by
    rw [entries_add, entries_omegaPow]
    exact addL_singleton_of_forall_lt (lt_omegaPow_iff.mp h))

/-- `ω^α` is additively indecomposable for the ordinal sum. -/
theorem add_lt_omegaPow {a x y : ThetaNote} (hx : x < omegaPow a) (hy : y < omegaPow a) :
    x + y < omegaPow a := by
  rw [lt_omegaPow_iff] at hx hy ⊢
  intro e he
  rw [entries_add] at he
  exact (mem_addL he).elim (hx e) (hy e)

/-! #### Principal terms

`Ω` and the terms `ϑ β` are ε-numbers: fixed points of `ω^·`, hence additively principal
(for both sums) and closed under `ω^·` from below (Freund §5, used in Theorem 6.7). -/

/-- `ω^α = α` exactly for the principal `α`. -/
theorem omegaPow_eq_self_iff {a : ThetaNote} : omegaPow a = a ↔ IsPrin a.1 := by
  constructor
  · intro h
    have h' := congrArg entries h
    rw [entries_omegaPow] at h'
    obtain ⟨t, ht⟩ := a
    cases t with
    | Omega => trivial
    | theta _ => trivial
    | sum xs =>
      exfalso
      change [sum xs] = xs at h'
      have hm : sum xs ∈ [sum xs] := List.mem_singleton_self _
      rw [h'] at hm
      exact absurd (l_lt_of_mem hm) (lt_irrefl _)
  · intro h
    exact Subtype.ext (ofList_singleton_prin h)

theorem omegaPow_Omega : omegaPow Omega = Omega := omegaPow_eq_self_iff.mpr trivial

theorem omegaPow_theta (b : ThetaNote) : omegaPow (theta b) = theta b :=
  omegaPow_eq_self_iff.mpr trivial

/-- Below a principal `P` are exactly the normal forms all of whose exponents are below `P`. -/
theorem lt_prin_iff {x p : ThetaNote} (hp : IsPrin p.1) : x < p ↔ ∀ e ∈ x.entries, e < p.1 := by
  conv_lhs => rw [← omegaPow_eq_self_iff.mpr hp]
  exact lt_omegaPow_iff

theorem nadd_lt_prin {x y p : ThetaNote} (hp : IsPrin p.1) (hx : x < p) (hy : y < p) :
    ThetaNote.nadd x y < p := by
  rw [← omegaPow_eq_self_iff.mpr hp] at hx hy ⊢
  exact nadd_lt_omegaPow hx hy

theorem add_lt_prin {x y p : ThetaNote} (hp : IsPrin p.1) (hx : x < p) (hy : y < p) :
    x + y < p := by
  rw [← omegaPow_eq_self_iff.mpr hp] at hx hy ⊢
  exact add_lt_omegaPow hx hy

theorem omegaPow_lt_prin {x p : ThetaNote} (hp : IsPrin p.1) (hx : x < p) : omegaPow x < p := by
  rw [← omegaPow_eq_self_iff.mpr hp]
  exact omegaPow_lt_omegaPow hx

theorem one_lt_prin {p : ThetaNote} (hp : IsPrin p.1) : one < p := by
  rw [lt_prin_iff hp, entries_one]
  intro e he
  rw [List.mem_singleton.mp he]
  exact nil_lt_prin hp

theorem succ_lt_prin {x p : ThetaNote} (hp : IsPrin p.1) (hx : x < p) : succ x < p :=
  nadd_lt_prin hp hx (one_lt_prin hp)

theorem ofNat_lt_prin {p : ThetaNote} (hp : IsPrin p.1) (n : ℕ) : ofNat n < p := by
  rw [lt_prin_iff hp, entries_ofNat]
  intro e he
  rw [List.eq_of_mem_replicate he]
  exact nil_lt_prin hp

/-- `ϑ β` is additively principal for the natural sum. -/
theorem nadd_lt_theta {x y b : ThetaNote} (hx : x < theta b) (hy : y < theta b) :
    ThetaNote.nadd x y < theta b :=
  nadd_lt_prin trivial hx hy

/-- `ϑ β` is additively principal for the ordinal sum. -/
theorem add_lt_theta {x y b : ThetaNote} (hx : x < theta b) (hy : y < theta b) :
    x + y < theta b :=
  add_lt_prin trivial hx hy

/-- `ϑ β` is closed under `ω^·` from below. -/
theorem omegaPow_lt_theta {x b : ThetaNote} (hx : x < theta b) : omegaPow x < theta b :=
  omegaPow_lt_prin trivial hx

theorem nadd_lt_Omega {x y : ThetaNote} (hx : x < Omega) (hy : y < Omega) :
    ThetaNote.nadd x y < Omega :=
  nadd_lt_prin trivial hx hy

theorem add_lt_Omega {x y : ThetaNote} (hx : x < Omega) (hy : y < Omega) : x + y < Omega :=
  add_lt_prin trivial hx hy

theorem omegaPow_lt_Omega {x : ThetaNote} (hx : x < Omega) : omegaPow x < Omega :=
  omegaPow_lt_prin trivial hx

/-! #### `ω · α` (Freund §5) -/

/-- `ω · α`: every exponent `α_i` of `α` is replaced by `1 + α_i`. -/
def omegaMul (a : ThetaNote) : ThetaNote :=
  ofEntries (a.entries.map onePlus)
    ⟨fun x hx => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        exact ((cnf_entries a).nf he).onePlus,
      List.pairwise_map.mpr ((sorted_entries a).imp_of_mem fun hx hy h =>
        onePlus_le_onePlus ((cnf_entries a).nf hy) ((cnf_entries a).nf hx) h)⟩

@[simp] theorem entries_omegaMul (a : ThetaNote) :
    (omegaMul a).entries = a.entries.map onePlus :=
  entries_ofEntries _ _

theorem omegaMul_lt_omegaMul {a b : ThetaNote} (h : a < b) : omegaMul a < omegaMul b := by
  rw [lt_iff_entries, entries_omegaMul, entries_omegaMul]
  exact sum_map_lt_sum_map (fun hx hy h => onePlus_lt_onePlus hx hy h)
    (cnf_entries a).1 (cnf_entries b).1 (lt_iff_entries.mp h)

theorem omegaMul_zero : omegaMul zero = zero := ext_entries (by simp)

/-- `ω · P = P` for principal `P`; in particular `ω · Ω = Ω` and `ω · ϑ β = ϑ β`. -/
theorem omegaMul_prin {p : ThetaNote} (hp : IsPrin p.1) : omegaMul p = p :=
  ext_entries (by
    rw [entries_omegaMul]
    unfold entries
    rw [toList_of_isPrin hp, List.map_singleton, onePlus_of_isPrin hp])

theorem omegaMul_Omega : omegaMul Omega = Omega := omegaMul_prin trivial

theorem omegaMul_theta (b : ThetaNote) : omegaMul (theta b) = theta b := omegaMul_prin trivial

/-- A principal `P` is closed under `ω · ·` from below. -/
theorem omegaMul_lt_prin {x p : ThetaNote} (hp : IsPrin p.1) (hx : x < p) : omegaMul x < p := by
  rw [lt_prin_iff hp] at hx ⊢
  rw [entries_omegaMul]
  intro e he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  have key : one + (show ThetaNote from ⟨d, (cnf_entries x).nf hd⟩) < p :=
    add_lt_prin hp (one_lt_prin hp) (hx d hd)
  exact key

end ThetaNote

end OrdinalAnalysis
