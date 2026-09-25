/-
  Arithmetic on the multi-level ϑ-notation, on the domain terms `ThetaWNoteD`.

  Source: A. Freund, arXiv:2204.09321, Definition 3.1 and §5, exactly as ported to the
  multi-level system by `Ordinal/ThetaW/{Basic,Order,Exponents}`; the term-level development
  below (the exponent-list operations `mergeL`, `addL`, `onePlus`) is `Ordinal/Theta/Arith.lean`
  verbatim with `ThetaTerm` replaced by `ThetaWTerm` — none of it uses anything about a single
  level, only the order and `IsPrin`, which are already proved uniformly in the level by
  `ThetaW/Order`.

  What is new here, and mandatory, is that `ThetaWNoteD := {t // NF t ∧ Dom t}` (`ThetaW/Dom`)
  carries the domain condition `Dom` as part of the type, so every operation must be shown to
  preserve it before it can be used on `ThetaWNoteD` at all.  The reason this is easy, uniformly,
  is `ThetaW/Dom`'s two structural facts:
  * `dom_ofList_iff : Dom (ofList xs) ↔ ∀ x ∈ xs, Dom x` (`Dom` of a Cantor sum is `Dom` of its
    exponents, for the sum built by `ofList`, which is what every operation below produces), and
  * `Dom.of_mem_toList : Dom t → x ∈ toList t → Dom x` (the exponents of a domain term are
    domain terms).
  So every operation's exponent list is built from the entries of its arguments by `List` combi-
  nators (`mergeL`, `addL`, `List.map`, `List.replicate`, `::`, `++`) together with the fixed
  domain terms `ThetaWTerm.zero` and `Ω_k`; `Dom` of the result is then exactly membership in one
  of the source lists, which the same combinators' membership lemmas (`mem_mergeL`, `mem_addL`,
  `List.mem_map`, …) already used for the order proofs hand over for free.  Each operation below
  therefore gets a one-line `dom_*` lemma extracting the `Dom` component of its own defining
  subtype element, stated separately (for uniformity) even though it adds no new work.

  What does *not* carry over: `Theta/Arith.lean`'s `theta : ThetaNote → ThetaNote` (an
  unconditional combinator, since the one-level system has no domain restriction) has no
  analogue here — `ThetaWTerm.theta k a` is in `ThetaWNoteD` only under the side condition
  `Dom a ∧ ∀ x ∈ G k a, x < a` (`ThetaW/Dom.dom_theta_iff`), which is not automatic in `a`.  So
  the specific corollaries `nadd_lt_theta`, `add_lt_theta`, `omegaPow_lt_theta`, `omegaMul_theta`
  of `Theta/Arith.lean` are replaced here by their general principal-term form (`nadd_lt_prin`,
  `add_lt_prin`, `omegaPow_lt_prin`, `omegaMul_prin`, all taking `IsPrin p.1` as a hypothesis),
  applied at a use site with whatever `Dom (theta k a)` proof is available there (as `ThetaW/Dom`
  already does for `c n` and `theta0Omega n`).  `Veblen.lean` supplies the domain side condition
  for the one new principal-adjacent term it needs, `φ_k`.
-/
import OrdinalAnalysis.Ordinal.ThetaW.Dom
import Mathlib.Data.List.Perm.Subperm

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

theorem ofList_injective {xs ys : List ThetaWTerm} (h : ofList xs = ofList ys) : xs = ys := by
  rw [← toList_ofList xs, ← toList_ofList ys, h]

theorem ofList_le_ofList {xs ys : List ThetaWTerm} : ofList xs ≤ ofList ys ↔ sum xs ≤ sum ys := by
  rw [le_def, le_def, ofList_lt_ofList]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (congrArg sum (ofList_injective h))
  · rintro (h | h)
    · exact Or.inl h
    · cases h; exact Or.inr rfl

/-! ### Non-increasing lists in pairwise form -/

/-- Non-increasing lists, in pairwise form (`Desc` unfolded). -/
abbrev SortedDesc (xs : List ThetaWTerm) : Prop := xs.Pairwise (fun x y => y ≤ x)

theorem CNF.sorted {xs : List ThetaWTerm} (h : CNF xs) : SortedDesc xs := h.2

theorem CNF.nf {xs : List ThetaWTerm} (h : CNF xs) {x : ThetaWTerm} (hx : x ∈ xs) : NF x :=
  h.1 x hx

theorem eq_of_perm_of_sortedDesc {xs ys : List ThetaWTerm} (hx : SortedDesc xs)
    (hy : SortedDesc ys) (h : xs.Perm ys) : xs = ys :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm' h2 h1) hx hy h

theorem SortedDesc.le_head {x : ThetaWTerm} {xs : List ThetaWTerm} (h : SortedDesc (x :: xs))
    {y : ThetaWTerm} (hy : y ∈ xs) : y ≤ x :=
  List.rel_of_pairwise_cons h hy

theorem not_le_iff_lt {a b : ThetaWTerm} (h : ¬ a ≤ b) : b < a := by
  rcases lt_trichotomy' a b with h' | rfl | h'
  · exact absurd (Or.inl h') h
  · exact absurd (le_refl' _) h
  · exact h'

/-! ### The merge of two non-increasing lists -/

/-- The comparison used by the merge: `x` goes first when `y ≼ x`. -/
def geb (x y : ThetaWTerm) : Bool := decide (y ≤ x)

/-- The merge of two lists; on non-increasing lists it is the non-increasing arrangement of
the union of the two multisets of entries. -/
def mergeL (xs ys : List ThetaWTerm) : List ThetaWTerm := List.merge xs ys geb

theorem mergeL_perm (xs ys : List ThetaWTerm) : (mergeL xs ys).Perm (xs ++ ys) :=
  List.merge_perm_append geb

@[simp] theorem mergeL_nil_left (ys : List ThetaWTerm) : mergeL [] ys = ys := List.nil_merge ys

@[simp] theorem mergeL_nil_right (xs : List ThetaWTerm) : mergeL xs [] = xs :=
  List.merge_right xs

theorem mem_mergeL {z : ThetaWTerm} {xs ys : List ThetaWTerm} :
    z ∈ mergeL xs ys ↔ z ∈ xs ∨ z ∈ ys :=
  List.mem_merge

theorem mergeL_cons_cons_of_le {x y : ThetaWTerm} (xs ys : List ThetaWTerm) (h : y ≤ x) :
    mergeL (x :: xs) (y :: ys) = x :: mergeL xs (y :: ys) :=
  List.cons_merge_cons_pos geb xs ys (by simp [geb, h])

theorem mergeL_cons_cons_of_lt {x y : ThetaWTerm} (xs ys : List ThetaWTerm) (h : x < y) :
    mergeL (x :: xs) (y :: ys) = y :: mergeL (x :: xs) ys :=
  List.cons_merge_cons_neg geb xs ys (by simp [geb, not_le_of_lt' h])

theorem sortedDesc_mergeL {xs ys : List ThetaWTerm} (hx : SortedDesc xs) (hy : SortedDesc ys) :
    SortedDesc (mergeL xs ys) := by
  have h := List.pairwise_merge (le := geb)
    (fun a b c hab hbc => by
      simp only [geb, decide_eq_true_eq] at hab hbc ⊢; exact le_trans' hbc hab)
    (fun a b => by
      rcases le_total' a b with h | h <;> simp [geb, h])
    xs ys (hx.imp (fun h => by simpa [geb] using h)) (hy.imp (fun h => by simpa [geb] using h))
  exact h.imp (fun h => by simpa [geb] using h)

theorem CNF.mergeL {xs ys : List ThetaWTerm} (hx : CNF xs) (hy : CNF ys) :
    CNF (mergeL xs ys) :=
  ⟨fun _ hz => (mem_mergeL.mp hz).elim hx.nf hy.nf, sortedDesc_mergeL hx.sorted hy.sorted⟩

/-- The merge is the unique non-increasing arrangement of the union. -/
theorem mergeL_eq_of_perm {xs ys zs : List ThetaWTerm} (hx : SortedDesc xs) (hy : SortedDesc ys)
    (hz : SortedDesc zs) (h : zs.Perm (xs ++ ys)) : mergeL xs ys = zs :=
  eq_of_perm_of_sortedDesc (sortedDesc_mergeL hx hy) hz ((mergeL_perm xs ys).trans h.symm)

theorem mergeL_comm {xs ys : List ThetaWTerm} (hx : SortedDesc xs) (hy : SortedDesc ys) :
    mergeL xs ys = mergeL ys xs :=
  mergeL_eq_of_perm hx hy (sortedDesc_mergeL hy hx)
    ((mergeL_perm ys xs).trans List.perm_append_comm)

theorem mergeL_assoc {xs ys zs : List ThetaWTerm} (hx : SortedDesc xs) (hy : SortedDesc ys)
    (hz : SortedDesc zs) : mergeL (mergeL xs ys) zs = mergeL xs (mergeL ys zs) := by
  refine mergeL_eq_of_perm (sortedDesc_mergeL hx hy) hz
    (sortedDesc_mergeL hx (sortedDesc_mergeL hy hz)) ?_
  refine (mergeL_perm _ _).trans ?_
  refine (List.Perm.append_left xs (mergeL_perm ys zs)).trans ?_
  refine List.Perm.trans ?_ (List.Perm.append_right zs (mergeL_perm xs ys).symm)
  rw [List.append_assoc]

/-- Moving an entry across a merge: `x :: xs` and `ys` merge like `xs` and `x :: ys`, when
`x` may head both lists. -/
theorem mergeL_cons_left_eq {x : ThetaWTerm} {xs ys : List ThetaWTerm}
    (hx : SortedDesc (x :: xs)) (hy : SortedDesc (x :: ys)) :
    mergeL xs (x :: ys) = mergeL (x :: xs) ys :=
  mergeL_eq_of_perm hx.of_cons hy (sortedDesc_mergeL hx (hy.of_cons))
    ((mergeL_perm _ _).trans List.perm_middle.symm)

/-- A non-increasing list is below its merge with a non-empty list. -/
theorem lt_mergeL_right : ∀ {ys zs : List ThetaWTerm}, SortedDesc ys → SortedDesc zs →
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
theorem mergeL_lt_mergeL_left : ∀ (ys : List ThetaWTerm) {xs xs' : List ThetaWTerm},
    SortedDesc xs → SortedDesc xs' → SortedDesc ys → sum xs < sum xs' →
    sum (mergeL xs ys) < sum (mergeL xs' ys)
  | [], xs, xs', _, _, _, h => by simpa using h
  | y :: ys, xs, xs', hx, hx', hy, h => by
    have IH := fun {xs xs' : List ThetaWTerm} => mergeL_lt_mergeL_left ys (xs := xs) (xs' := xs')
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

theorem sum_append_lt_sum_append (zs : List ThetaWTerm) {xs ys : List ThetaWTerm}
    (h : sum xs < sum ys) : sum (zs ++ xs) < sum (zs ++ ys) := by
  induction zs with
  | nil => exact h
  | cons z zs ih => exact (cons_lt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, ih⟩)

/-- A proper extension of a sum is larger. -/
theorem sum_lt_sum_append (xs : List ThetaWTerm) (y : ThetaWTerm) (ys : List ThetaWTerm) :
    sum xs < sum (xs ++ y :: ys) := by
  induction xs with
  | nil => exact nil_lt_cons y ys
  | cons x xs ih => exact (cons_lt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, ih⟩)

/-- Exercise 3.2(d), second part, in multiset form. -/
theorem sum_le_sum_of_forall₂ {as cs : List ThetaWTerm} (hr : List.Forall₂ (· ≤ ·) as cs) :
    ∀ {bs : List ThetaWTerm}, Desc bs → cs.Subperm bs → sum as ≤ sum bs := by
  induction hr with
  | nil => intro bs _ _; exact nil_le _
  | @cons a c as cs hac _ ih =>
    intro bs hd hs
    cases bs with
    | nil => exact absurd (hs.subset List.mem_cons_self) (by simp)
    | cons b bs =>
      have hcb : c ≤ b := hd.le_head c (hs.subset List.mem_cons_self)
      rcases le_trans' hac hcb with hab | rfl
      · exact Or.inl ((cons_lt_cons_iff _ _ _ _).mpr (Or.inl hab))
      · have hc : c = a := le_antisymm' hcb hac
        subst hc
        rcases ih hd.tail ((List.subperm_cons c).mp hs) with h | h
        · exact Or.inl ((cons_lt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, h⟩))
        · cases h; exact le_refl' _

/-- A non-increasing list is below `⟨α⟩` iff all its entries are below `α`. -/
theorem sum_lt_singleton_iff {xs : List ThetaWTerm} (hx : SortedDesc xs) (a : ThetaWTerm) :
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
theorem sum_lt_cons_of_forall_lt {xs : List ThetaWTerm} {b : ThetaWTerm} (bs : List ThetaWTerm)
    (h : ∀ x ∈ xs, x < b) : sum xs < sum (b :: bs) := by
  cases xs with
  | nil => exact nil_lt_cons b bs
  | cons x xs => exact (cons_lt_cons_iff _ _ _ _).mpr (Or.inl (h x List.mem_cons_self))

/-! ### The ordinal sum of exponent lists -/

/-- The exponent list of `α + β`. -/
def addL (xs : List ThetaWTerm) : List ThetaWTerm → List ThetaWTerm
  | [] => xs
  | y :: ys => xs.filter (fun x => geb x y) ++ y :: ys

@[simp] theorem addL_nil (xs : List ThetaWTerm) : addL xs [] = xs := rfl

theorem addL_cons (xs : List ThetaWTerm) (y : ThetaWTerm) (ys : List ThetaWTerm) :
    addL xs (y :: ys) = xs.filter (fun x => geb x y) ++ y :: ys := rfl

@[simp] theorem nil_addL (ys : List ThetaWTerm) : addL [] ys = ys := by
  cases ys <;> rfl

theorem mem_filter_geb {x y : ThetaWTerm} {xs : List ThetaWTerm} :
    x ∈ xs.filter (fun x => geb x y) ↔ x ∈ xs ∧ y ≤ x := by
  simp [geb]

theorem mem_addL {z : ThetaWTerm} {xs ys : List ThetaWTerm} (h : z ∈ addL xs ys) :
    z ∈ xs ∨ z ∈ ys := by
  cases ys with
  | nil => exact Or.inl h
  | cons y ys =>
    rcases List.mem_append.mp h with h | h
    · exact Or.inl (mem_filter_geb.mp h).1
    · exact Or.inr h

theorem sortedDesc_addL {xs ys : List ThetaWTerm} (hx : SortedDesc xs) (hy : SortedDesc ys) :
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

theorem CNF.addL {xs ys : List ThetaWTerm} (hx : CNF xs) (hy : CNF ys) : CNF (addL xs ys) :=
  ⟨fun _ hz => (mem_addL hz).elim hx.nf hy.nf, sortedDesc_addL hx.sorted hy.sorted⟩

/-- Associativity of the ordinal sum, on exponent lists. -/
theorem addL_assoc (xs : List ThetaWTerm) {ys : List ThetaWTerm} (hy : SortedDesc ys)
    (zs : List ThetaWTerm) : addL (addL xs ys) zs = addL xs (addL ys zs) := by
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
theorem exists_filter_append {xs : List ThetaWTerm} (hx : SortedDesc xs) (t : ThetaWTerm) :
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
theorem addL_lt_addL_right {xs ys ys' : List ThetaWTerm} (hx : SortedDesc xs)
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
theorem mergeL_nil_singleton {xs : List ThetaWTerm} (hx : SortedDesc xs) :
    mergeL xs [sum []] = xs ++ [sum []] := by
  refine mergeL_eq_of_perm hx (List.pairwise_singleton _ _) ?_ (List.Perm.refl _)
  unfold SortedDesc
  rw [List.pairwise_append]
  refine ⟨hx, List.pairwise_singleton _ _, fun a _ b hb => ?_⟩
  rw [List.mem_singleton.mp hb]
  exact nil_le a

/-- `α + 1` on exponent lists: `xs` followed by `0`. -/
theorem addL_nil_singleton (xs : List ThetaWTerm) : addL xs [sum []] = xs ++ [sum []] := by
  rw [addL_cons, List.filter_eq_self.mpr]
  intro x _
  simp [geb, nil_le x]

/-- If every entry of `xs` is below `a`, then `xs` is absorbed: `α + ω^a = ω^a`. -/
theorem addL_singleton_of_forall_lt {xs : List ThetaWTerm} {a : ThetaWTerm}
    (h : ∀ x ∈ xs, x < a) : addL xs [a] = [a] := by
  rw [addL_cons, List.filter_eq_nil_iff.mpr, List.nil_append]
  intro x hx
  simp only [geb, decide_eq_true_eq]
  exact not_le_of_lt' (h x hx)

/-! ### `1 + α` on terms, for `ω · α` -/

/-- The term `1 + α`. -/
def onePlus (e : ThetaWTerm) : ThetaWTerm := ofList (addL [sum []] (toList e))

theorem NF.onePlus {e : ThetaWTerm} (h : NF e) : NF (onePlus e) :=
  nf_ofList_iff.mpr (CNF.addL ⟨by simp [nf_zero'], List.pairwise_singleton _ _⟩ h.cnf_toList)
where nf_zero' : NF (sum []) := nf_zero

/-- `1 + α` preserves `Dom`: its exponents are `0` (`Dom` trivially) and the exponents of `e`,
which are `Dom` since `e` is. -/
theorem Dom.onePlus {e : ThetaWTerm} (h : Dom e) : Dom (onePlus e) :=
  dom_ofList_iff.mpr (fun x hx => (mem_addL hx).elim
    (fun hx' => by rw [List.mem_singleton] at hx'; exact hx' ▸ dom_zero)
    (fun hx' => h.of_mem_toList hx'))

theorem onePlus_lt_onePlus {e e' : ThetaWTerm} (he : NF e) (he' : NF e') (h : e < e') :
    onePlus e < onePlus e' := by
  unfold onePlus
  rw [ofList_lt_ofList]
  refine addL_lt_addL_right (List.pairwise_singleton _ _) ?_
  rwa [← ofList_lt_ofList, ofList_toList he, ofList_toList he']

theorem onePlus_le_onePlus {e e' : ThetaWTerm} (he : NF e) (he' : NF e') (h : e ≤ e') :
    onePlus e ≤ onePlus e' := by
  rcases h with h | rfl
  · exact Or.inl (onePlus_lt_onePlus he he' h)
  · exact le_refl' _

/-- `1 + P = P` for principal `P`. -/
theorem onePlus_of_isPrin {p : ThetaWTerm} (hp : IsPrin p) : onePlus p = p := by
  unfold onePlus
  rw [toList_of_isPrin hp, addL_cons, List.filter_eq_nil_iff.mpr, List.nil_append,
    ofList_singleton_prin hp]
  intro x hx
  rw [List.mem_singleton.mp hx]
  simp only [geb, decide_eq_true_eq]
  rintro (h | h)
  · exact not_prin_lt_nil hp h
  · cases p with
    | Omega _ => cases h
    | theta _ _ => cases h
    | sum _ => exact hp

/-- A strictly monotone map on normal entries preserves the order of exponent lists. -/
theorem sum_map_lt_sum_map {f : ThetaWTerm → ThetaWTerm}
    (hf : ∀ {x y : ThetaWTerm}, NF x → NF y → x < y → f x < f y) :
    ∀ {xs ys : List ThetaWTerm}, (∀ x ∈ xs, NF x) → (∀ y ∈ ys, NF y) → sum xs < sum ys →
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

end ThetaWTerm

/-! ### The operations on `ThetaWNoteD` -/

namespace ThetaWNoteD

open ThetaWTerm

/-- The Cantor exponents of a domain normal form. -/
def entries (a : ThetaWNoteD) : List ThetaWTerm := toList a.1

theorem cnf_entries (a : ThetaWNoteD) : CNF a.entries := NF.cnf_toList a.2.1

theorem sorted_entries (a : ThetaWNoteD) : SortedDesc a.entries := (cnf_entries a).sorted

/-- The exponents of a domain term are domain terms. -/
theorem dom_entries (a : ThetaWNoteD) : ∀ x ∈ a.entries, Dom x := fun _ hx =>
  Dom.of_mem_toList a.2.2 hx

/-- The domain notation with a given non-increasing list of normal, domain exponents. -/
def ofEntries (xs : List ThetaWTerm) (h : CNF xs) (hd : ∀ x ∈ xs, Dom x) : ThetaWNoteD :=
  ⟨ofList xs, nf_ofList_iff.mpr h, dom_ofList_iff.mpr hd⟩

@[simp] theorem entries_ofEntries (xs : List ThetaWTerm) (h : CNF xs) (hd : ∀ x ∈ xs, Dom x) :
    (ofEntries xs h hd).entries = xs :=
  toList_ofList xs

theorem ext_entries {a b : ThetaWNoteD} (h : a.entries = b.entries) : a = b := by
  apply Subtype.ext
  calc a.1 = ofList (toList a.1) := (ofList_toList a.2.1).symm
    _ = ofList (toList b.1) := congrArg ofList h
    _ = b.1 := ofList_toList b.2.1

/-- The order of domain notations is the lexicographic order of their exponent lists. -/
theorem lt_iff_entries {a b : ThetaWNoteD} : a < b ↔ sum a.entries < sum b.entries := by
  show a.1 < b.1 ↔ _
  unfold entries
  rw [← ofList_lt_ofList, ofList_toList a.2.1, ofList_toList b.2.1]

theorem le_iff_entries {a b : ThetaWNoteD} : a ≤ b ↔ sum a.entries ≤ sum b.entries := by
  show a.1 ≤ b.1 ↔ _
  unfold entries
  rw [← ofList_le_ofList, ofList_toList a.2.1, ofList_toList b.2.1]

@[simp] theorem entries_zero : zero.entries = [] := rfl

@[simp] theorem entries_Omega (k : ℕ) : (Omega k).entries = [ThetaWTerm.Omega k] := rfl

theorem bot_eq_zero : (⊥ : ThetaWNoteD) = zero := rfl

/-! #### The natural sum -/

/-- The natural (Hessenberg) sum: the merge of the exponent lists. -/
def nadd (a b : ThetaWNoteD) : ThetaWNoteD :=
  ofEntries (mergeL a.entries b.entries) ((cnf_entries a).mergeL (cnf_entries b))
    (fun z hz => (mem_mergeL.mp hz).elim (dom_entries a z) (dom_entries b z))

@[simp] theorem entries_nadd (a b : ThetaWNoteD) :
    (nadd a b).entries = mergeL a.entries b.entries :=
  entries_ofEntries _ _ _

/-- `nadd` preserves `Dom` (by construction; stated separately as required). -/
theorem dom_nadd (a b : ThetaWNoteD) : Dom (nadd a b).1 := (nadd a b).2.2

theorem nadd_comm (a b : ThetaWNoteD) : nadd a b = nadd b a :=
  ext_entries (by simp only [entries_nadd]; exact mergeL_comm (sorted_entries a) (sorted_entries b))

theorem nadd_assoc (a b c : ThetaWNoteD) : nadd (nadd a b) c = nadd a (nadd b c) :=
  ext_entries (by
    simp only [entries_nadd]
    exact mergeL_assoc (sorted_entries a) (sorted_entries b) (sorted_entries c))

theorem nadd_zero (a : ThetaWNoteD) : nadd a zero = a :=
  ext_entries (by simp)

theorem zero_nadd (a : ThetaWNoteD) : nadd zero a = a :=
  ext_entries (by simp)

theorem nadd_lt_nadd_left {a a' : ThetaWNoteD} (b : ThetaWNoteD) (h : a < a') :
    nadd a b < nadd a' b := by
  rw [lt_iff_entries, entries_nadd, entries_nadd]
  exact mergeL_lt_mergeL_left _ (sorted_entries a) (sorted_entries a') (sorted_entries b)
    (lt_iff_entries.mp h)

theorem nadd_lt_nadd_right (a : ThetaWNoteD) {b b' : ThetaWNoteD} (h : b < b') :
    nadd a b < nadd a b' := by
  rw [nadd_comm a b, nadd_comm a b']
  exact nadd_lt_nadd_left a h

theorem nadd_le_nadd_right (a : ThetaWNoteD) {b b' : ThetaWNoteD} (h : b ≤ b') :
    nadd a b ≤ nadd a b' := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (nadd_lt_nadd_right a h)
  · exact le_rfl

theorem le_nadd_left (a b : ThetaWNoteD) : a ≤ nadd a b := by
  have h := nadd_le_nadd_right a (bot_le : (⊥ : ThetaWNoteD) ≤ b)
  rwa [bot_eq_zero, nadd_zero] at h

theorem le_nadd_right (a b : ThetaWNoteD) : b ≤ nadd a b := by
  rw [nadd_comm]; exact le_nadd_left b a

/-! #### `ω^·` -/

/-- `ω^α`: the domain notation with the single exponent `α`. -/
def omegaPow (a : ThetaWNoteD) : ThetaWNoteD :=
  ofEntries [a.1] ⟨fun x hx => by rw [List.mem_singleton] at hx; exact hx ▸ a.2.1,
      List.pairwise_singleton _ _⟩
    (fun x hx => by rw [List.mem_singleton] at hx; exact hx ▸ a.2.2)

@[simp] theorem entries_omegaPow (a : ThetaWNoteD) : (omegaPow a).entries = [a.1] :=
  entries_ofEntries _ _ _

/-- `ω^·` preserves `Dom` (by construction; stated separately as required). -/
theorem dom_omegaPow (a : ThetaWNoteD) : Dom (omegaPow a).1 := (omegaPow a).2.2

theorem omegaPow_lt_omegaPow {a b : ThetaWNoteD} (h : a < b) : omegaPow a < omegaPow b := by
  rw [lt_iff_entries, entries_omegaPow, entries_omegaPow]
  exact (cons_lt_cons_iff _ _ _ _).mpr (Or.inl h)

theorem omegaPow_le_omegaPow {a b : ThetaWNoteD} (h : a ≤ b) : omegaPow a ≤ omegaPow b := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (omegaPow_lt_omegaPow h)
  · exact le_rfl

theorem omegaPow_lt_omegaPow_iff {a b : ThetaWNoteD} : omegaPow a < omegaPow b ↔ a < b :=
  ⟨fun h => lt_of_not_ge fun h' => absurd h (not_lt_of_ge (omegaPow_le_omegaPow h')),
    omegaPow_lt_omegaPow⟩

theorem omegaPow_injective {a b : ThetaWNoteD} (h : omegaPow a = omegaPow b) : a = b := by
  have := congrArg entries h
  simp only [entries_omegaPow, List.cons.injEq, and_true] at this
  exact Subtype.ext this

/-- Below `ω^α` are exactly the domain notations all of whose exponents are below `α`. -/
theorem lt_omegaPow_iff {x a : ThetaWNoteD} : x < omegaPow a ↔ ∀ e ∈ x.entries, e < a.1 := by
  rw [lt_iff_entries, entries_omegaPow]
  exact sum_lt_singleton_iff (sorted_entries x) a.1

/-- `ω^α` is additively indecomposable for the natural sum. -/
theorem nadd_lt_omegaPow {a x y : ThetaWNoteD} (hx : x < omegaPow a) (hy : y < omegaPow a) :
    nadd x y < omegaPow a := by
  rw [lt_omegaPow_iff] at hx hy ⊢
  intro e he
  rw [entries_nadd] at he
  exact (mem_mergeL.mp he).elim (hx e) (hy e)

/-! #### `1`, the numerals and the successor -/

/-- `1 = ω^0 = ⟨0⟩`. -/
def one : ThetaWNoteD := omegaPow zero

theorem one_eq_omegaPow_zero : one = omegaPow zero := rfl

@[simp] theorem entries_one : one.entries = [ThetaWTerm.sum []] := rfl

theorem dom_one : Dom one.1 := dom_omegaPow zero

theorem one_le_omegaPow (a : ThetaWNoteD) : one ≤ omegaPow a :=
  omegaPow_le_omegaPow (bot_le : (⊥ : ThetaWNoteD) ≤ a)

theorem zero_lt_one : zero < one := by
  rw [lt_iff_entries]; exact nil_lt_cons _ _

/-- The numeral `n = ⟨0, …, 0⟩` (`n` entries). -/
def ofNat (n : ℕ) : ThetaWNoteD :=
  ofEntries (List.replicate n (ThetaWTerm.sum []))
    ⟨fun x hx => by rw [List.eq_of_mem_replicate hx]; exact nf_zero,
      List.pairwise_replicate.mpr (Or.inr (le_refl' _))⟩
    (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact dom_zero)

@[simp] theorem entries_ofNat (n : ℕ) :
    (ofNat n).entries = List.replicate n (ThetaWTerm.sum []) :=
  entries_ofEntries _ _ _

theorem dom_ofNat (n : ℕ) : Dom (ofNat n).1 := (ofNat n).2.2

theorem ofNat_zero : ofNat 0 = zero := ext_entries (by simp)

theorem ofNat_one : ofNat 1 = one := ext_entries (by simp)

theorem ofNat_lt_ofNat {m n : ℕ} (h : m < n) : ofNat m < ofNat n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [lt_iff_entries, entries_ofNat, entries_ofNat, show m + k + 1 = m + (k + 1) by omega,
    List.replicate_add, List.replicate_succ]
  exact sum_lt_sum_append _ _ _

theorem entries_nadd_one (a : ThetaWNoteD) :
    (nadd a one).entries = a.entries ++ [ThetaWTerm.sum []] := by
  rw [entries_nadd, entries_one, mergeL_nil_singleton (sorted_entries a)]

theorem lt_nadd_one (a : ThetaWNoteD) : a < nadd a one := by
  rw [lt_iff_entries, entries_nadd_one]
  exact sum_lt_sum_append _ _ _

/-- The successor `α + 1`, as `α ⊕ 1`. -/
def succ (a : ThetaWNoteD) : ThetaWNoteD := nadd a one

theorem lt_succ (a : ThetaWNoteD) : a < succ a := lt_nadd_one a

theorem dom_succ (a : ThetaWNoteD) : Dom (succ a).1 := dom_nadd a one

theorem ofNat_succ (n : ℕ) : ofNat (n + 1) = succ (ofNat n) :=
  ext_entries (by rw [succ, entries_nadd_one, entries_ofNat, entries_ofNat, List.replicate_succ'])

/-! #### The ordinal sum -/

/-- The ordinal sum `α + β`. -/
def add (a b : ThetaWNoteD) : ThetaWNoteD :=
  ofEntries (addL a.entries b.entries) ((cnf_entries a).addL (cnf_entries b))
    (fun z hz => (mem_addL hz).elim (dom_entries a z) (dom_entries b z))

instance : Add ThetaWNoteD := ⟨add⟩

theorem add_def (a b : ThetaWNoteD) : a + b = add a b := rfl

@[simp] theorem entries_add (a b : ThetaWNoteD) :
    (a + b).entries = addL a.entries b.entries := by
  rw [add_def]; exact entries_ofEntries _ _ _

/-- The ordinal sum preserves `Dom` (by construction; stated separately as required). -/
theorem dom_add (a b : ThetaWNoteD) : Dom (a + b).1 := (add a b).2.2

/-- The ordinal sum is associative. -/
theorem add_assoc (a b c : ThetaWNoteD) : a + b + c = a + (b + c) :=
  ext_entries (by simp only [entries_add]; exact addL_assoc _ (sorted_entries b) _)

theorem add_zero (a : ThetaWNoteD) : a + zero = a := ext_entries (by simp)

theorem zero_add (a : ThetaWNoteD) : zero + a = a := ext_entries (by simp)

/-- The ordinal sum is strictly monotone in its right argument. -/
theorem add_lt_add_left (a : ThetaWNoteD) {b c : ThetaWNoteD} (h : b < c) : a + b < a + c := by
  rw [lt_iff_entries, entries_add, entries_add]
  exact addL_lt_addL_right (sorted_entries a) (lt_iff_entries.mp h)

theorem add_le_add_left (a : ThetaWNoteD) {b c : ThetaWNoteD} (h : b ≤ c) : a + b ≤ a + c := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (add_lt_add_left a h)
  · exact le_rfl

theorem le_add_left (a b : ThetaWNoteD) : b ≤ a + b := by
  rw [le_iff_entries, entries_add]
  cases hb : b.entries with
  | nil => exact nil_le _
  | cons y ys =>
    have hs : SortedDesc (addL a.entries (y :: ys)) :=
      sortedDesc_addL (sorted_entries a) (hb ▸ sorted_entries b)
    rw [addL_cons] at hs ⊢
    exact sum_le_sum_of_forall₂ (List.forall₂_same.mpr fun x _ => le_refl' x)
      (desc_iff_pairwise.mpr hs) (List.sublist_append_right _ _).subperm

theorem add_one_eq_succ (a : ThetaWNoteD) : a + one = succ a :=
  ext_entries (by rw [succ, entries_nadd_one, entries_add, entries_one, addL_nil_singleton])

/-- `α + ω^β = ω^β` whenever `α ≺ ω^β`. -/
theorem add_omegaPow_of_lt {x a : ThetaWNoteD} (h : x < omegaPow a) : x + omegaPow a = omegaPow a :=
  ext_entries (by
    rw [entries_add, entries_omegaPow]
    exact addL_singleton_of_forall_lt (lt_omegaPow_iff.mp h))

/-- `ω^α` is additively indecomposable for the ordinal sum. -/
theorem add_lt_omegaPow {a x y : ThetaWNoteD} (hx : x < omegaPow a) (hy : y < omegaPow a) :
    x + y < omegaPow a := by
  rw [lt_omegaPow_iff] at hx hy ⊢
  intro e he
  rw [entries_add] at he
  exact (mem_addL he).elim (hx e) (hy e)

/-! #### Principal terms

`Ω_{k+1}` and the terms `ϑ_k β` are ε-numbers: fixed points of `ω^·`, hence additively principal
(for both sums) and closed under `ω^·` from below, exactly as in the one-level system
(`Ordinal/Theta/Arith.lean`) — the argument is entirely about `IsPrin`, uniform in the level. -/

/-- `ω^α = α` exactly for the principal `α`. -/
theorem omegaPow_eq_self_iff {a : ThetaWNoteD} : omegaPow a = a ↔ IsPrin a.1 := by
  constructor
  · intro h
    have h' := congrArg entries h
    rw [entries_omegaPow] at h'
    obtain ⟨t, ht⟩ := a
    cases t with
    | Omega _ => trivial
    | theta _ _ => trivial
    | sum xs =>
      exfalso
      change [ThetaWTerm.sum xs] = xs at h'
      have hm : ThetaWTerm.sum xs ∈ [ThetaWTerm.sum xs] := List.mem_singleton_self _
      rw [h'] at hm
      exact absurd (l_lt_of_mem hm) (lt_irrefl _)
  · intro h
    exact Subtype.ext (ofList_singleton_prin h)

theorem omegaPow_Omega (k : ℕ) : omegaPow (Omega k) = Omega k := omegaPow_eq_self_iff.mpr trivial

/-- Below a principal `P` are exactly the domain notations all of whose exponents are below
`P`. -/
theorem lt_prin_iff {x p : ThetaWNoteD} (hp : IsPrin p.1) : x < p ↔ ∀ e ∈ x.entries, e < p.1 := by
  conv_lhs => rw [← omegaPow_eq_self_iff.mpr hp]
  exact lt_omegaPow_iff

theorem nadd_lt_prin {x y p : ThetaWNoteD} (hp : IsPrin p.1) (hx : x < p) (hy : y < p) :
    nadd x y < p := by
  rw [← omegaPow_eq_self_iff.mpr hp] at hx hy ⊢
  exact nadd_lt_omegaPow hx hy

theorem add_lt_prin {x y p : ThetaWNoteD} (hp : IsPrin p.1) (hx : x < p) (hy : y < p) :
    x + y < p := by
  rw [← omegaPow_eq_self_iff.mpr hp] at hx hy ⊢
  exact add_lt_omegaPow hx hy

theorem omegaPow_lt_prin {x p : ThetaWNoteD} (hp : IsPrin p.1) (hx : x < p) : omegaPow x < p := by
  rw [← omegaPow_eq_self_iff.mpr hp]
  exact omegaPow_lt_omegaPow hx

theorem one_lt_prin {p : ThetaWNoteD} (hp : IsPrin p.1) : one < p := by
  rw [lt_prin_iff hp, entries_one]
  intro e he
  rw [List.mem_singleton.mp he]
  exact nil_lt_prin hp

theorem succ_lt_prin {x p : ThetaWNoteD} (hp : IsPrin p.1) (hx : x < p) : succ x < p :=
  nadd_lt_prin hp hx (one_lt_prin hp)

theorem ofNat_lt_prin {p : ThetaWNoteD} (hp : IsPrin p.1) (n : ℕ) : ofNat n < p := by
  rw [lt_prin_iff hp, entries_ofNat]
  intro e he
  rw [List.eq_of_mem_replicate he]
  exact nil_lt_prin hp

theorem nadd_lt_Omega {k : ℕ} {x y : ThetaWNoteD} (hx : x < Omega k) (hy : y < Omega k) :
    nadd x y < Omega k :=
  nadd_lt_prin trivial hx hy

theorem add_lt_Omega {k : ℕ} {x y : ThetaWNoteD} (hx : x < Omega k) (hy : y < Omega k) :
    x + y < Omega k :=
  add_lt_prin trivial hx hy

theorem omegaPow_lt_Omega {k : ℕ} {x : ThetaWNoteD} (hx : x < Omega k) : omegaPow x < Omega k :=
  omegaPow_lt_prin trivial hx

/-- `α + Ω_{k+1} = Ω_{k+1}` whenever `α ≺ Ω_{k+1}`. -/
theorem add_Omega_of_lt {k : ℕ} {x : ThetaWNoteD} (h : x < Omega k) : x + Omega k = Omega k := by
  rw [← omegaPow_Omega k] at h ⊢
  exact add_omegaPow_of_lt h

/-! #### `ω · α` (Freund §5) -/

/-- `ω · α`: every exponent `α_i` of `α` is replaced by `1 + α_i`. -/
def omegaMul (a : ThetaWNoteD) : ThetaWNoteD :=
  ofEntries (a.entries.map onePlus)
    ⟨fun x hx => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        exact ((cnf_entries a).nf he).onePlus,
      List.pairwise_map.mpr ((sorted_entries a).imp_of_mem fun hx hy h =>
        onePlus_le_onePlus ((cnf_entries a).nf hy) ((cnf_entries a).nf hx) h)⟩
    (fun x hx => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        exact Dom.onePlus (dom_entries a e he))

@[simp] theorem entries_omegaMul (a : ThetaWNoteD) :
    (omegaMul a).entries = a.entries.map onePlus :=
  entries_ofEntries _ _ _

/-- `ω · ·` preserves `Dom` (by construction; stated separately as required). -/
theorem dom_omegaMul (a : ThetaWNoteD) : Dom (omegaMul a).1 := (omegaMul a).2.2

theorem omegaMul_lt_omegaMul {a b : ThetaWNoteD} (h : a < b) : omegaMul a < omegaMul b := by
  rw [lt_iff_entries, entries_omegaMul, entries_omegaMul]
  exact sum_map_lt_sum_map (fun hx hy h => onePlus_lt_onePlus hx hy h)
    (cnf_entries a).1 (cnf_entries b).1 (lt_iff_entries.mp h)

theorem omegaMul_zero : omegaMul zero = zero := ext_entries (by simp)

/-- `ω · P = P` for principal `P`; in particular `ω · Ω_{k+1} = Ω_{k+1}`. -/
theorem omegaMul_prin {p : ThetaWNoteD} (hp : IsPrin p.1) : omegaMul p = p :=
  ext_entries (by
    rw [entries_omegaMul]
    unfold entries
    rw [toList_of_isPrin hp, List.map_singleton, onePlus_of_isPrin hp])

theorem omegaMul_Omega (k : ℕ) : omegaMul (Omega k) = Omega k := omegaMul_prin trivial

/-- A principal `P` is closed under `ω · ·` from below. -/
theorem omegaMul_lt_prin {x p : ThetaWNoteD} (hp : IsPrin p.1) (hx : x < p) : omegaMul x < p := by
  rw [lt_prin_iff hp] at hx ⊢
  rw [entries_omegaMul]
  intro e he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  have key : one + (show ThetaWNoteD from ⟨d, (cnf_entries x).nf hd, dom_entries x d hd⟩) < p :=
    add_lt_prin hp (one_lt_prin hp) (hx d hd)
  exact key

end ThetaWNoteD

end OrdinalAnalysis
