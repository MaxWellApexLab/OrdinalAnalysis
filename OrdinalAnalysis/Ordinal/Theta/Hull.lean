/-
  The hulls `C^α(β)` and the Buchholz operators `H_α` on the ϑ-notation.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Definition 3.8, Proposition 3.9, Definition 3.10,
  Proposition 3.11 (after Buchholz, Lemma 4.7 of his 1992 paper on local predicativity),
  and Definition 5.4 with Exercise 5.5 (closure operators, nice operators, `H[Z]`).

  * `C^α(β)` is the least set of notations that contains `Ω` and every `γ ≺ β`, contains
    `ϑ γ` whenever it contains `γ` and `γ ≺ α`, and contains a sum `⟨γ₀, …, γ_{n-1}⟩`
    whenever it contains every `γ_i` (Definition 3.8).  It is given as an inductive
    predicate on raw terms, restricted to the normal forms; since the subterms of a normal
    form are normal, this is exactly the set of Definition 3.8 (`Cset_subset_of_closed`
    and the closure lemmas).
  * Proposition 3.9: `γ ∈ C^α(β) ⇔ E(γ) ⊆ C^α(β)`, and
    `ϑ α = min {γ | C^α(γ) ∩ Ω ≺* γ and α ∈ C^α(γ)}`.
  * `H_α(X) = ⋂ {C^γ(δ) | α ≺ γ and X ⊆ C^γ(δ)}`, the whole notation system when the
    family is empty (Definition 3.10), and Proposition 3.11 (a)–(c).
  * Operators, nice operators, `H[Z](X) = H(Z ∪ X)` (Definition 5.4), and Exercise 5.5
    (a)–(d) together with the ordinal part of (e): a nice operator is closed under `+`,
    the natural sum, `ω · ·` and `ω^·`.  The coefficient facts `E(α + β) ⊆ E(α) ∪ E(β)`,
    `E(ω^α) = E(α)`, `E(ω · α) ⊆ E(α)` needed for this are proved here.
  * The facts about `H_α` that the collapsing theorem (Theorem 6.7) uses: the hypothesis
    `X ⊆ ⋂ {C^ξ(ϑ ξ) | α ≺ ξ}` (`HullHyp`) and its consequences, `α ≺ α + ω(β)`,
    `η = α + ω(β) ∈ H_η(X)` and `ϑ η ∈ H_η(X)` for `α, β ∈ H_α(X)`, and
    `α + ω(β') + ω(β') ≺ α + ω(β)` for `β' ≺ β`.

  Sets of notations are `Set ThetaNote`; `E(α)` as a set of notations is `Ehull α`.
-/
import OrdinalAnalysis.Ordinal.Theta.WellFounded
import Mathlib.Order.Bounds.Defs
import Mathlib.Data.Set.Lattice

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaTerm

/-! ### Coefficients of the Cantor exponents -/

/-- `E(α)` is the union of the `E(e)` over the Cantor exponents `e` of `α`. -/
theorem mem_E_iff_toList_hull {t g : ThetaTerm} : g ∈ E t ↔ ∃ e ∈ toList t, g ∈ E e := by
  cases t with
  | Omega => simp
  | theta a => simp
  | sum xs => exact mem_E_sum

/-- `E(1 + α) ⊆ E(α)`. -/
theorem mem_E_of_mem_E_onePlus_hull {e g : ThetaTerm} (h : g ∈ E (onePlus e)) : g ∈ E e := by
  unfold onePlus at h
  obtain ⟨x, hx, hg⟩ := mem_E_ofList.mp h
  rcases mem_addL hx with hx | hx
  · rw [List.mem_singleton.mp hx] at hg; simp at hg
  · exact mem_E_iff_toList_hull.mpr ⟨x, hx, hg⟩

/-! ### The hulls on raw terms -/

/-- The generating clauses of `C^α(β)` (Freund, Definition 3.8), on raw terms. -/
inductive CsetT (a b : ThetaTerm) : ThetaTerm → Prop
  /-- Clause (i): `Ω ∈ C^α(β)`. -/
  | ofOmega : CsetT a b Omega
  /-- Clause (i): `γ ∈ C^α(β)` for `γ ≺ β`. -/
  | ofLt {g : ThetaTerm} : g < b → CsetT a b g
  /-- Clause (ii): `γ ∈ C^α(β)` and `γ ≺ α` give `ϑ γ ∈ C^α(β)`. -/
  | ofTheta {g : ThetaTerm} : CsetT a b g → g < a → CsetT a b (theta g)
  /-- Clause (iii): `⟨γ₀, …, γ_{n-1}⟩ ∈ C^α(β)` when every `γ_i ∈ C^α(β)`. -/
  | ofSum {xs : List ThetaTerm} : (∀ x ∈ xs, CsetT a b x) → CsetT a b (sum xs)

/-- Proposition 3.9, right to left: `E(γ) ⊆ C^α(β)` gives `γ ∈ C^α(β)` (on all raw terms). -/
theorem CsetT.of_E {a b : ThetaTerm} : ∀ {g : ThetaTerm}, (∀ d ∈ E g, CsetT a b d) →
    CsetT a b g
  | Omega, _ => .ofOmega
  | theta _, h => h _ (by simp)
  | sum xs, h => .ofSum fun x hx => CsetT.of_E (fun d hd => h d (mem_E_of_mem hx hd))
termination_by g => l g
decreasing_by exact l_lt_of_mem hx

/-- Proposition 3.9, left to right: for normal `γ`, `γ ∈ C^α(β)` gives `E(γ) ⊆ C^α(β)`. -/
theorem CsetT.E_sub {a b g : ThetaTerm} (h : CsetT a b g) (hg : NF g) :
    ∀ d ∈ E g, CsetT a b d := by
  revert hg
  induction h with
  | ofOmega => intro _ d hd; simp at hd
  | ofLt hlt =>
    intro hg d hd
    exact .ofLt (lt_of_le_of_lt' (le_of_mem_E hg hd) hlt)
  | ofTheta h1 h2 _ =>
    intro _ d hd
    simp only [E_theta, List.mem_singleton] at hd
    subst hd
    exact .ofTheta h1 h2
  | ofSum _ ih =>
    intro hg d hd
    obtain ⟨x, hx, hdx⟩ := mem_E_sum.mp hd
    exact ih x hx (hg.of_mem hx) d hdx

theorem CsetT.iff_E {a b g : ThetaTerm} (hg : NF g) :
    CsetT a b g ↔ ∀ d ∈ E g, CsetT a b d :=
  ⟨fun h => h.E_sub hg, CsetT.of_E⟩

/-- Proposition 3.9, first half of the proof of the minimum: `C^α(ϑ α) ∩ Ω ≺* ϑ α`, by
induction on the length. -/
theorem lt_theta_of_CsetT_theta {a : ThetaTerm} : ∀ {d : ThetaTerm}, NF d →
    CsetT a (theta a) d → d < Omega → d < theta a
  | Omega, _, _, h => absurd h not_Omega_lt_Omega
  | theta d', hn, hc, _ => by
    cases hc with
    | ofLt h => exact h
    | ofTheta h1 h2 =>
      refine theta_lt_theta_of_lt h2 fun g hg => ?_
      exact lt_theta_of_CsetT_theta ((nf_theta_iff d').mp hn |>.of_mem_E hg)
        (h1.E_sub ((nf_theta_iff d').mp hn) g hg) (lt_Omega_of_mem_E hg)
  | sum [], _, _, _ => nil_lt_theta a
  | sum (x :: xs), hn, hc, hΩ => by
    cases hc with
    | ofLt h => exact h
    | ofSum h =>
      rw [cons_lt_theta_iff]
      exact lt_theta_of_CsetT_theta (hn.of_mem List.mem_cons_self) (h x List.mem_cons_self)
        ((cons_lt_Omega_iff x xs).mp hΩ)
termination_by d => l d
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · simp; omega

/-- Proposition 3.9, second half of the proof of the minimum: if `C^α(γ) ∩ Ω ≺* γ` and
`α ∈ C^α(γ)`, then every normal `δ ≺ ϑ α` lies in `C^α(γ)`, by induction on the length. -/
theorem CsetT_of_lt_theta {a c : ThetaTerm} (ha : NF a)
    (hc : ∀ d, NF d → CsetT a c d → d < Omega → d < c) (hac : CsetT a c a) :
    ∀ {d : ThetaTerm}, NF d → d < theta a → CsetT a c d
  | Omega, _, h => absurd h (not_Omega_lt_theta a)
  | theta d', hn, h => by
    rcases (theta_lt_theta_iff d' a).mp h with ⟨h1, h2⟩ | ⟨g, hg, hle⟩
    · refine .ofTheta (CsetT.of_E fun g hg => ?_) h1
      exact CsetT_of_lt_theta ha hc hac ((nf_theta_iff d').mp hn |>.of_mem_E hg) (h2 g hg)
    · have hgC : CsetT a c g := hac.E_sub ha g hg
      exact .ofLt (lt_of_le_of_lt' hle
        (hc g (ha.of_mem_E hg) hgC (lt_Omega_of_mem_E hg)))
  | sum [], _, _ => .ofSum (by simp)
  | sum (y :: ys), hn, h => by
    refine .ofSum fun x hx => ?_
    have hle : x ≤ y := hn.desc.le_head x hx
    exact CsetT_of_lt_theta ha hc hac (hn.of_mem hx)
      (lt_of_le_of_lt' hle ((cons_lt_theta_iff y a ys).mp h))
termination_by d => l d
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · exact l_lt_of_mem hx

end ThetaTerm

namespace ThetaNote

open ThetaTerm

/-! ### Coefficient sets of notations -/

/-- The set `E(α)` of Freund, Definition 3.1, as a set of notations. -/
def Ehull (a : ThetaNote) : Set ThetaNote := {g | g.1 ∈ E a.1}

theorem mem_Ehull {a g : ThetaNote} : g ∈ Ehull a ↔ g.1 ∈ E a.1 := Iff.rfl

theorem mem_Ehull_iff_entries_hull {a g : ThetaNote} :
    g ∈ Ehull a ↔ ∃ e ∈ a.entries, g.1 ∈ E e :=
  mem_E_iff_toList_hull

@[simp] theorem Ehull_Omega_hull : Ehull Omega = ∅ := by
  ext g; change g.1 ∈ E ThetaTerm.Omega ↔ False; simp

@[simp] theorem Ehull_zero_hull : Ehull zero = ∅ := by
  ext g; change g.1 ∈ E (sum []) ↔ False; simp

theorem Ehull_theta_hull (b : ThetaNote) : Ehull (theta b) = {theta b} := by
  ext g
  change g.1 ∈ E (ThetaTerm.theta b.1) ↔ g = theta b
  simp only [E_theta, List.mem_singleton]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

/-- `E(α + β) ⊆ E(α) ∪ E(β)`. -/
theorem Ehull_add_subset_hull (a b : ThetaNote) : Ehull (a + b) ⊆ Ehull a ∪ Ehull b := by
  intro g hg
  obtain ⟨e, he, hge⟩ := mem_Ehull_iff_entries_hull.mp hg
  rw [entries_add] at he
  rcases mem_addL he with he | he
  · exact Or.inl (mem_Ehull_iff_entries_hull.mpr ⟨e, he, hge⟩)
  · exact Or.inr (mem_Ehull_iff_entries_hull.mpr ⟨e, he, hge⟩)

/-- `E(α ⊕ β) ⊆ E(α) ∪ E(β)`. -/
theorem Ehull_nadd_subset_hull (a b : ThetaNote) :
    Ehull (ThetaNote.nadd a b) ⊆ Ehull a ∪ Ehull b := by
  intro g hg
  obtain ⟨e, he, hge⟩ := mem_Ehull_iff_entries_hull.mp hg
  rw [entries_nadd] at he
  rcases mem_mergeL.mp he with he | he
  · exact Or.inl (mem_Ehull_iff_entries_hull.mpr ⟨e, he, hge⟩)
  · exact Or.inr (mem_Ehull_iff_entries_hull.mpr ⟨e, he, hge⟩)

/-- `E(ω^α) = E(α)`. -/
theorem Ehull_omegaPow_hull (a : ThetaNote) : Ehull (omegaPow a) = Ehull a := by
  ext g
  rw [mem_Ehull_iff_entries_hull, entries_omegaPow]
  simp [mem_Ehull]

/-- `E(ω · α) ⊆ E(α)`. -/
theorem Ehull_omegaMul_subset_hull (a : ThetaNote) : Ehull (omegaMul a) ⊆ Ehull a := by
  intro g hg
  obtain ⟨e, he, hge⟩ := mem_Ehull_iff_entries_hull.mp hg
  rw [entries_omegaMul] at he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  exact mem_Ehull_iff_entries_hull.mpr ⟨d, hd, mem_E_of_mem_E_onePlus_hull hge⟩

@[simp] theorem Ehull_one_hull : Ehull one = ∅ := by
  rw [one, Ehull_omegaPow_hull, Ehull_zero_hull]

@[simp] theorem Ehull_ofNat_hull (n : ℕ) : Ehull (ofNat n) = ∅ := by
  ext g
  simp only [mem_Ehull_iff_entries_hull, entries_ofNat, Set.mem_empty_iff_false, iff_false]
  rintro ⟨e, he, hg⟩
  rw [List.eq_of_mem_replicate he] at hg
  simp at hg

theorem Ehull_succ_subset_hull (a : ThetaNote) : Ehull (succ a) ⊆ Ehull a := by
  intro g hg
  rcases Ehull_nadd_subset_hull a one hg with h | h
  · exact h
  · simp at h

/-! ### The hulls `C^α(β)` (Definition 3.8) -/

/-- The set `C^α(β)` of Freund, Definition 3.8. -/
def Cset (a b : ThetaNote) : Set ThetaNote := {g | CsetT a.1 b.1 g.1}

theorem mem_Cset {a b g : ThetaNote} : g ∈ Cset a b ↔ CsetT a.1 b.1 g.1 := Iff.rfl

/-- Definition 3.8 (i): `Ω ∈ C^α(β)`. -/
theorem Omega_mem_Cset (a b : ThetaNote) : Omega ∈ Cset a b := CsetT.ofOmega

/-- Definition 3.8 (i): `γ ∈ C^α(β)` for `γ ≺ β`. -/
theorem mem_Cset_of_lt {a b g : ThetaNote} (h : g < b) : g ∈ Cset a b := CsetT.ofLt h

/-- Definition 3.8 (ii): `γ ∈ C^α(β)` and `γ ≺ α` give `ϑ γ ∈ C^α(β)`. -/
theorem theta_mem_Cset {a b g : ThetaNote} (h : g ∈ Cset a b) (hg : g < a) :
    theta g ∈ Cset a b := CsetT.ofTheta h hg

/-- Definition 3.8 (iii): a sum `⟨γ₀, …, γ_{n-1}⟩` lies in `C^α(β)` when every `γ_i` does. -/
theorem sum_mem_Cset {a b g : ThetaNote} {xs : List ThetaTerm} (hg : g.1 = sum xs)
    (h : ∀ x : ThetaNote, x.1 ∈ xs → x ∈ Cset a b) : g ∈ Cset a b := by
  rw [mem_Cset, hg]
  have hn : NF (sum xs) := hg ▸ g.2
  exact CsetT.ofSum fun x hx => h ⟨x, hn.of_mem hx⟩ hx

/-- Definition 3.8: `C^α(β)` is the least set of notations closed under the clauses (i)–(iii). -/
theorem Cset_subset_of_closed {a b : ThetaNote} (S : Set ThetaNote) (h0 : Omega ∈ S)
    (h1 : ∀ g, g < b → g ∈ S) (h2 : ∀ g ∈ S, g < a → theta g ∈ S)
    (h3 : ∀ (g : ThetaNote) (xs : List ThetaTerm), g.1 = sum xs →
      (∀ x : ThetaNote, x.1 ∈ xs → x ∈ S) → g ∈ S) :
    Cset a b ⊆ S := by
  suffices key : ∀ t, CsetT a.1 b.1 t → ∀ ht : NF t, (⟨t, ht⟩ : ThetaNote) ∈ S from
    fun g hg => key g.1 hg g.2
  intro t ht
  induction ht with
  | ofOmega => intro _; exact h0
  | ofLt h => intro hn; exact h1 ⟨_, hn⟩ h
  | ofTheta _ hlt ih =>
    intro hn
    exact h2 ⟨_, (nf_theta_iff _).mp hn⟩ (ih ((nf_theta_iff _).mp hn)) hlt
  | @ofSum xs _ ih =>
    intro hn
    exact h3 ⟨sum xs, hn⟩ xs rfl fun x hx => ih x.1 hx x.2

/-! ### Proposition 3.9 -/

/-- Proposition 3.9, first part: `γ ∈ C^α(β) ⇔ E(γ) ⊆ C^α(β)`. -/
theorem mem_Cset_iff_Ehull_subset {a b g : ThetaNote} : g ∈ Cset a b ↔ Ehull g ⊆ Cset a b := by
  rw [mem_Cset, CsetT.iff_E g.2]
  constructor
  · intro h d hd
    exact h d.1 hd
  · intro h d hd
    exact h (a := ⟨d, g.2.of_mem_E hd⟩) hd

/-- `α ∈ C^α(ϑ α)` (Freund, proof of Proposition 3.9). -/
theorem mem_Cset_theta_self (a : ThetaNote) : a ∈ Cset a (theta a) :=
  mem_Cset_iff_Ehull_subset.mpr fun _ hg => mem_Cset_of_lt (lt_theta_of_mem_E hg)

/-- `C^α(ϑ α) ∩ Ω ≺* ϑ α` (Freund, proof of Proposition 3.9): `δ ∈ C^α(ϑ α)` and `δ ≺ Ω`
give `δ ≺ ϑ α`. -/
theorem lt_theta_of_mem_Cset {a d : ThetaNote} (hd : d ∈ Cset a (theta a))
    (hΩ : d < Omega) : d < theta a :=
  lt_theta_of_CsetT_theta d.2 hd hΩ

/-- Proposition 3.9, second part:
`ϑ α = min {γ | C^α(γ) ∩ Ω ≺* γ and α ∈ C^α(γ)}`. -/
theorem theta_isLeast (a : ThetaNote) :
    IsLeast {c : ThetaNote | (∀ d ∈ Cset a c, d < Omega → d < c) ∧ a ∈ Cset a c} (theta a) := by
  refine ⟨⟨fun d hd hΩ => lt_theta_of_mem_Cset hd hΩ, mem_Cset_theta_self a⟩, ?_⟩
  rintro c ⟨hc, hac⟩
  by_contra hlt
  have hlt : c < theta a := lt_of_not_ge hlt
  have hcC : c ∈ Cset a c :=
    CsetT_of_lt_theta a.2 (fun d hdn hdC hdΩ => hc ⟨d, hdn⟩ hdC hdΩ) hac c.2 hlt
  exact absurd (hc c hcC (lt_trans hlt (theta_lt_Omega a))) (lt_irrefl c)

/-! ### The operators `H_α` (Definition 3.10) -/

/-- The operator `H_α` of Freund, Definition 3.10:
`H_α(X) = ⋂ {C^γ(δ) | α ≺ γ and X ⊆ C^γ(δ)}`, which is the set of all notations when no
`C^γ(δ)` qualifies. -/
def Hop (a : ThetaNote) (X : Set ThetaNote) : Set ThetaNote :=
  {x | ∀ c d : ThetaNote, a < c → X ⊆ Cset c d → x ∈ Cset c d}

theorem mem_Hop {a x : ThetaNote} {X : Set ThetaNote} :
    x ∈ Hop a X ↔ ∀ c d : ThetaNote, a < c → X ⊆ Cset c d → x ∈ Cset c d := Iff.rfl

/-- Definition 3.10, as an intersection of a family of sets. -/
theorem Hop_eq_sInter (a : ThetaNote) (X : Set ThetaNote) :
    Hop a X = ⋂₀ {S | ∃ c d : ThetaNote, a < c ∧ X ⊆ Cset c d ∧ S = Cset c d} := by
  ext x
  simp only [Set.mem_sInter, Set.mem_ofPred_eq, mem_Hop]
  constructor
  · rintro h S ⟨c, d, hac, hX, rfl⟩
    exact h c d hac hX
  · intro h c d hac hX
    exact h _ ⟨c, d, hac, hX, rfl⟩

/-- Definition 3.10: `H_α(X)` is everything when the family of sets is empty. -/
theorem Hop_eq_univ {a : ThetaNote} {X : Set ThetaNote}
    (h : ∀ c d : ThetaNote, a < c → ¬ X ⊆ Cset c d) : Hop a X = Set.univ :=
  Set.eq_univ_of_forall fun _ c d hac hX => absurd hX (h c d hac)

theorem Hop_subset_Cset {a c d : ThetaNote} {X : Set ThetaNote} (hac : a < c)
    (hX : X ⊆ Cset c d) : Hop a X ⊆ Cset c d :=
  fun _ hx => hx c d hac hX

/-! ### Proposition 3.11 -/

/-- Proposition 3.11 (a): `α ≺ β` gives `H_α(X) ⊆ H_β(X)`. -/
theorem Hop_subset_Hop {a b : ThetaNote} (h : a < b) (X : Set ThetaNote) :
    Hop a X ⊆ Hop b X :=
  fun _ hx c d hbc hX => hx c d (lt_trans h hbc) hX

theorem Hop_subset_Hop_of_le {a b : ThetaNote} (h : a ≤ b) (X : Set ThetaNote) :
    Hop a X ⊆ Hop b X := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact Hop_subset_Hop h X
  · exact le_rfl

/-- Proposition 3.11 (b): `α ∈ H_β(X)` and `α ≼ β` give `ϑ α ∈ H_β(X)`. -/
theorem theta_mem_Hop {a b : ThetaNote} {X : Set ThetaNote} (ha : a ∈ Hop b X) (hab : a ≤ b) :
    theta a ∈ Hop b X :=
  fun c d hbc hX => theta_mem_Cset (ha c d hbc hX) (lt_of_le_of_lt hab hbc)

/-- Proposition 3.11 (c): if `X ⊆ ⋂ {C^γ(ϑ γ) | α ≺ γ}`, then `α ≼ β ≺ γ` and
`β ∈ H_α(X)` give `ϑ β ≺ ϑ γ`. -/
theorem theta_lt_theta_of_mem_Hop {a b c : ThetaNote} {X : Set ThetaNote}
    (hX : X ⊆ ⋂ (c : ThetaNote) (_ : a < c), Cset c (theta c)) (hab : a ≤ b) (hbc : b < c)
    (hb : b ∈ Hop a X) : theta b < theta c := by
  have h1 : theta b ∈ Hop b X := theta_mem_Hop (Hop_subset_Hop_of_le hab X hb) le_rfl
  have hXc : X ⊆ Cset c (theta c) := fun x hx =>
    Set.mem_iInter₂.mp (hX hx) c (lt_of_le_of_lt hab hbc)
  exact lt_theta_of_mem_Cset (h1 c (theta c) hbc hXc) (theta_lt_Omega b)

/-! ### Operators (Definition 5.4) -/

/-- A closure operator (Freund, Definition 5.4): `X ⊆ H(X)`, and `X ⊆ H(Y)` gives
`H(X) ⊆ H(Y)`. -/
def IsOperator (H : Set ThetaNote → Set ThetaNote) : Prop :=
  (∀ X, X ⊆ H X) ∧ ∀ X Y, X ⊆ H Y → H X ⊆ H Y

/-- A nice operator (Freund, Definition 5.4): an operator with `α ∈ H(X) ⇔ E(α) ⊆ H(X)`. -/
def Nice (H : Set ThetaNote → Set ThetaNote) : Prop :=
  IsOperator H ∧ ∀ (X : Set ThetaNote) (a : ThetaNote), a ∈ H X ↔ Ehull a ⊆ H X

/-- The operator `H[Z]` of Freund, Definition 5.4: `H[Z](X) = H(Z ∪ X)`. -/
def adjoin (H : Set ThetaNote → Set ThetaNote) (Z : Set ThetaNote) :
    Set ThetaNote → Set ThetaNote :=
  fun X => H (Z ∪ X)

theorem adjoin_apply (H : Set ThetaNote → Set ThetaNote) (Z X : Set ThetaNote) :
    adjoin H Z X = H (Z ∪ X) := rfl

theorem IsOperator.subset {H : Set ThetaNote → Set ThetaNote} (hH : IsOperator H)
    (X : Set ThetaNote) : X ⊆ H X :=
  hH.1 X

/-- Exercise 5.5 (b): an operator is monotone. -/
theorem IsOperator.mono {H : Set ThetaNote → Set ThetaNote} (hH : IsOperator H)
    {X Y : Set ThetaNote} (h : X ⊆ Y) : H X ⊆ H Y :=
  hH.2 X Y (h.trans (hH.1 Y))

theorem IsOperator.idem {H : Set ThetaNote → Set ThetaNote} (hH : IsOperator H)
    (X : Set ThetaNote) : H (H X) = H X :=
  le_antisymm (hH.2 _ _ le_rfl) (hH.1 _)

theorem Nice.isOperator {H : Set ThetaNote → Set ThetaNote} (hH : Nice H) : IsOperator H := hH.1

theorem Nice.mem_iff {H : Set ThetaNote → Set ThetaNote} (hH : Nice H) {X : Set ThetaNote}
    {a : ThetaNote} : a ∈ H X ↔ Ehull a ⊆ H X :=
  hH.2 X a

/-- Exercise 5.5 (a): `H_α` is an operator. -/
theorem Hop_isOperator (a : ThetaNote) : IsOperator (Hop a) :=
  ⟨fun _ _ hx _ _ _ hX => hX hx,
    fun _ _ hXY _ hx c d hac hY => hx c d hac fun _ hy => hXY hy c d hac hY⟩

/-- Exercise 5.5 (a): `H_α` is a nice operator (by Proposition 3.9). -/
theorem Hop_nice (a : ThetaNote) : Nice (Hop a) :=
  ⟨Hop_isOperator a, fun _ _ =>
    ⟨fun hx _ hg c d hac hX => mem_Cset_iff_Ehull_subset.mp (hx c d hac hX) hg,
      fun h c d hac hX => mem_Cset_iff_Ehull_subset.mpr fun _ hg => h hg c d hac hX⟩⟩

theorem Hop_mono {a : ThetaNote} {X Y : Set ThetaNote} (h : X ⊆ Y) : Hop a X ⊆ Hop a Y :=
  (Hop_isOperator a).mono h

/-- Exercise 5.5 (c): `H[Z]` is an operator when `H` is. -/
theorem IsOperator.adjoin {H : Set ThetaNote → Set ThetaNote} (hH : IsOperator H)
    (Z : Set ThetaNote) : IsOperator (adjoin H Z) :=
  ⟨fun _ => Set.subset_union_right.trans (hH.1 _),
    fun _ _ h => hH.2 _ _ (Set.union_subset (Set.subset_union_left.trans (hH.1 _)) h)⟩

/-- Exercise 5.5 (c): `H[Z]` is nice when `H` is. -/
theorem Nice.adjoin {H : Set ThetaNote → Set ThetaNote} (hH : Nice H) (Z : Set ThetaNote) :
    Nice (adjoin H Z) :=
  ⟨hH.1.adjoin Z, fun X a => hH.2 (Z ∪ X) a⟩

/-- Exercise 5.5 (c): `H[Z] = H` when `Z ⊆ H(∅)`. -/
theorem adjoin_eq_self {H : Set ThetaNote → Set ThetaNote} (hH : IsOperator H)
    {Z : Set ThetaNote} (hZ : Z ⊆ H ∅) : adjoin H Z = H := by
  funext X
  exact le_antisymm
    (hH.2 _ _ (Set.union_subset (hZ.trans (hH.mono (Set.empty_subset X))) (hH.1 X)))
    (hH.mono Set.subset_union_right)

/-- Exercise 5.5 (c): `H[Z][Z'] = H[Z ∪ Z']`. -/
theorem adjoin_adjoin (H : Set ThetaNote → Set ThetaNote) (Z Z' : Set ThetaNote) :
    adjoin (adjoin H Z) Z' = adjoin H (Z ∪ Z') := by
  funext X
  simp only [adjoin, Set.union_assoc]

/-- The niceness condition, derived from the two clauses of Exercise 5.5 (d), by induction
on the length. -/
theorem mem_iff_Ehull_subset_of_clauses {S : Set ThetaNote} (hΩ : Omega ∈ S)
    (hsum : ∀ (g : ThetaNote) (xs : List ThetaTerm), g.1 = sum xs →
      (g ∈ S ↔ ∀ x : ThetaNote, x.1 ∈ xs → x ∈ S)) :
    ∀ (t : ThetaTerm) (ht : NF t), (⟨t, ht⟩ : ThetaNote) ∈ S ↔ Ehull ⟨t, ht⟩ ⊆ S
  | ThetaTerm.Omega, _ => by
    constructor
    · intro _ d hd
      have hd' : d.1 ∈ E ThetaTerm.Omega := hd
      simp at hd'
    · intro _
      exact hΩ
  | ThetaTerm.theta s, ht => by
    constructor
    · intro h d hd
      have hd' : d.1 ∈ E (ThetaTerm.theta s) := hd
      simp only [E_theta, List.mem_singleton] at hd'
      have hd'' : d = ⟨ThetaTerm.theta s, ht⟩ := Subtype.ext hd'
      subst hd''
      exact h
    · intro h
      exact h (show ThetaTerm.theta s ∈ E (ThetaTerm.theta s) by simp)
  | ThetaTerm.sum xs, ht => by
    refine (hsum ⟨sum xs, ht⟩ xs rfl).trans ?_
    constructor
    · intro h d hd
      obtain ⟨x, hx, hdx⟩ := mem_E_sum.mp hd
      exact (mem_iff_Ehull_subset_of_clauses hΩ hsum x (ht.of_mem hx)).mp (h ⟨x, _⟩ hx) hdx
    · intro h x hx
      exact (mem_iff_Ehull_subset_of_clauses hΩ hsum x.1 x.2).mpr
        fun d hd => h (mem_E_of_mem hx hd)
termination_by t => l t
decreasing_by
  · exact l_lt_of_mem hx
  · exact l_lt_of_mem hx

/-- Exercise 5.5 (d): an operator `H` is nice precisely when every `H(X)` contains `Ω` and
contains a sum `⟨α₀, …, α_{n-1}⟩` exactly when it contains every `α_i`. -/
theorem nice_iff {H : Set ThetaNote → Set ThetaNote} :
    Nice H ↔ IsOperator H ∧ ∀ X, Omega ∈ H X ∧
      ∀ (g : ThetaNote) (xs : List ThetaTerm), g.1 = sum xs →
        (g ∈ H X ↔ ∀ x : ThetaNote, x.1 ∈ xs → x ∈ H X) := by
  constructor
  · intro hH
    refine ⟨hH.1, fun X => ⟨hH.mem_iff.mpr (by simp), fun g xs hg => ?_⟩⟩
    constructor
    · intro h x hx
      refine hH.mem_iff.mpr fun d hd => hH.mem_iff.mp h ?_
      show d.1 ∈ E g.1
      rw [hg]
      exact mem_E_of_mem hx hd
    · intro h
      refine hH.mem_iff.mpr fun d hd => ?_
      have hd' : d.1 ∈ E (sum xs) := hg ▸ hd
      obtain ⟨x, hx, hdx⟩ := mem_E_sum.mp hd'
      have hxn : NF x := (hg ▸ g.2 : NF (sum xs)).of_mem hx
      exact hH.mem_iff.mp (h ⟨x, hxn⟩ hx) hdx
  · rintro ⟨hH, h⟩
    exact ⟨hH, fun X a => mem_iff_Ehull_subset_of_clauses (h X).1 (h X).2 a.1 a.2⟩

/-! ### Exercise 5.5 (e): closure of nice operators under the arithmetic -/

section Nice

variable {H : Set ThetaNote → Set ThetaNote} (hH : Nice H) {X : Set ThetaNote}
include hH

theorem Nice.Omega_mem : Omega ∈ H X := hH.mem_iff.mpr (by simp)

theorem Nice.zero_mem : zero ∈ H X := hH.mem_iff.mpr (by simp)

theorem Nice.one_mem : one ∈ H X := hH.mem_iff.mpr (by simp)

theorem Nice.ofNat_mem (n : ℕ) : ofNat n ∈ H X := hH.mem_iff.mpr (by simp)

/-- Exercise 5.5 (e): `α, β ∈ H(X)` give `α + β ∈ H(X)`. -/
theorem Nice.add_mem {a b : ThetaNote} (ha : a ∈ H X) (hb : b ∈ H X) : a + b ∈ H X :=
  hH.mem_iff.mpr ((Ehull_add_subset_hull a b).trans
    (Set.union_subset (hH.mem_iff.mp ha) (hH.mem_iff.mp hb)))

theorem Nice.nadd_mem {a b : ThetaNote} (ha : a ∈ H X) (hb : b ∈ H X) :
    ThetaNote.nadd a b ∈ H X :=
  hH.mem_iff.mpr ((Ehull_nadd_subset_hull a b).trans
    (Set.union_subset (hH.mem_iff.mp ha) (hH.mem_iff.mp hb)))

/-- Exercise 5.5 (e): `α ∈ H(X)` gives `ω · α ∈ H(X)`. -/
theorem Nice.omegaMul_mem {a : ThetaNote} (ha : a ∈ H X) : omegaMul a ∈ H X :=
  hH.mem_iff.mpr ((Ehull_omegaMul_subset_hull a).trans (hH.mem_iff.mp ha))

/-- Exercise 5.5 (e): `α ∈ H(X)` gives `ω(α) = ω^α ∈ H(X)`. -/
theorem Nice.omegaPow_mem {a : ThetaNote} (ha : a ∈ H X) : omegaPow a ∈ H X :=
  hH.mem_iff.mpr ((Ehull_omegaPow_hull a).symm ▸ hH.mem_iff.mp ha)

theorem Nice.succ_mem {a : ThetaNote} (ha : a ∈ H X) : succ a ∈ H X :=
  hH.mem_iff.mpr ((Ehull_succ_subset_hull a).trans (hH.mem_iff.mp ha))

end Nice

/-! ### The facts about `H_α` used in the collapsing theorem (Freund, Theorem 6.7) -/

/-- The hypothesis `X ⊆ ⋂ {C^ξ(ϑ ξ) | α ≺ ξ}` of Proposition 3.11 (c) and Theorem 6.7. -/
def HullHyp (a : ThetaNote) (X : Set ThetaNote) : Prop :=
  X ⊆ ⋂ (c : ThetaNote) (_ : a < c), Cset c (theta c)

theorem hullHyp_iff {a : ThetaNote} {X : Set ThetaNote} :
    HullHyp a X ↔ ∀ c, a < c → X ⊆ Cset c (theta c) := by
  unfold HullHyp
  constructor
  · intro h c hac x hx
    exact Set.mem_iInter₂.mp (h hx) c hac
  · intro h x hx
    exact Set.mem_iInter₂.mpr fun c hac => h c hac hx

theorem HullHyp.subset_Cset {a c : ThetaNote} {X : Set ThetaNote} (h : HullHyp a X)
    (hac : a < c) : X ⊆ Cset c (theta c) :=
  hullHyp_iff.mp h c hac

/-- The hypothesis passes to larger indices (`α ≺ η` in Theorem 6.7). -/
theorem HullHyp.mono {a b : ThetaNote} {X : Set ThetaNote} (h : HullHyp a X) (hab : a ≤ b) :
    HullHyp b X :=
  hullHyp_iff.mpr fun _ hbc => h.subset_Cset (lt_of_le_of_lt hab hbc)

/-- `H_α(X) ⊆ C^ξ(ϑ ξ)` for `α ≺ ξ` (Theorem 6.7, via Definition 3.10). -/
theorem HullHyp.Hop_subset {a c : ThetaNote} {X : Set ThetaNote} (h : HullHyp a X)
    (hac : a < c) : Hop a X ⊆ Cset c (theta c) :=
  Hop_subset_Cset hac (h.subset_Cset hac)

/-- `δ ∈ H_α(X)` and `δ ≺ Ω` give `δ ≺ ϑ ξ` for `α ≺ ξ` (Theorem 6.7, via Proposition 3.9). -/
theorem HullHyp.lt_theta {a c d : ThetaNote} {X : Set ThetaNote} (h : HullHyp a X)
    (hac : a < c) (hd : d ∈ Hop a X) (hΩ : d < Omega) : d < theta c :=
  lt_theta_of_mem_Cset (h.Hop_subset hac hd) hΩ

/-- The case of clause (V) in Theorem 6.7: `δ ∈ H_α(X)`, `δ ≺ Ω` and `γ ≺ δ` give the
hypothesis for `X ∪ {γ}`. -/
theorem HullHyp.union_singleton {a d g : ThetaNote} {X : Set ThetaNote} (h : HullHyp a X)
    (hd : d ∈ Hop a X) (hΩ : d < Omega) (hgd : g < d) : HullHyp a (X ∪ {g}) :=
  hullHyp_iff.mpr fun _ hac => Set.union_subset (h.subset_Cset hac)
    (Set.singleton_subset_iff.mpr (mem_Cset_of_lt (lt_trans hgd (h.lt_theta hac hd hΩ))))

/-- `α ≺ α + ω(β)`. -/
theorem lt_add_omegaPow_hull (a b : ThetaNote) : a < a + omegaPow b := by
  have h := add_lt_add_left a (lt_of_lt_of_le zero_lt_one (one_le_omegaPow b))
  rwa [add_zero] at h

/-- `α + ω(β') + ω(β') ≺ α + ω(β)` for `β' ≺ β` (Theorem 6.7, the cut of rank `Ω`). -/
theorem add_omegaPow_add_omegaPow_lt_hull (a : ThetaNote) {b b' : ThetaNote} (h : b' < b) :
    a + omegaPow b' + omegaPow b' < a + omegaPow b := by
  rw [add_assoc]
  exact add_lt_add_left a (add_lt_omegaPow (omegaPow_lt_omegaPow h) (omegaPow_lt_omegaPow h))

/-- Theorem 6.7: from `α, β ∈ H_α(X)` we get `η = α + ω(β) ∈ H_η(X)` (Exercise 5.5 and
Proposition 3.11 (a)). -/
theorem add_omegaPow_mem_Hop {a b : ThetaNote} {X : Set ThetaNote} (ha : a ∈ Hop a X)
    (hb : b ∈ Hop a X) : a + omegaPow b ∈ Hop (a + omegaPow b) X :=
  Hop_subset_Hop (lt_add_omegaPow_hull a b) X
    ((Hop_nice a).add_mem ha ((Hop_nice a).omegaPow_mem hb))

/-- Theorem 6.7: from `α, β ∈ H_α(X)` we get `ϑ η ∈ H_η(X)` for `η = α + ω(β)`
(Proposition 3.11 (b)). -/
theorem theta_add_omegaPow_mem_Hop {a b : ThetaNote} {X : Set ThetaNote} (ha : a ∈ Hop a X)
    (hb : b ∈ Hop a X) : theta (a + omegaPow b) ∈ Hop (a + omegaPow b) X :=
  theta_mem_Hop (add_omegaPow_mem_Hop ha hb) le_rfl

end ThetaNote

end OrdinalAnalysis
