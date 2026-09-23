/-
  The boundedness lemma for `ACA_∞`.

  A cut-free derivation of height `α` in the evaluating second-order ω-calculus,
  all of whose formulas lie in the class `InCe₂`, cannot prove `TI₂(≺, X)`.  This
  is `Gentzen/Boundedness.lean` with `ev` replaced by `ev₂` and `Xat n̄` by
  `n̄ ∈ X`; the invariant is the two-parameter reading of the design notes,
  unchanged:

  * `n̄ ∈ X` reads as "the ordinal coded by `n` is below `δ`";
  * `n̄ ∉ X` reads as "the ordinal coded by `n` is **not** below `γ`";
  * `∼Prog₂(≺, X)` has **no** reading at all;
  * the remaining members read as their positive content bounded by `δ`.

  The lemma says: for every `γ`, a derivation of height `α` has a member true
  under the reading `(γ, γ ⊕ ω^α)`.  The one case with content is `∃` on
  `∼Prog₂`, which re-invokes the induction hypothesis at the raised lower bound
  `succ (γ ⊕ ω^β)`; the ordinal arithmetic that pays for it is
  `Gentzen.Boundedness.bump_le`, reused verbatim — it is generic in
  `[OrdinalNotation O]` and says nothing about the syntax.

  Three cases are new relative to the first-order proof.

  * **`identity` is general.**  The second-order calculus derives `[φ, ∼φ]` for
    *every* `φ`, so the induction meets a sequent both of whose members are in
    the class.  `good₂_or_good₂_neg` settles it: by `InCe₂.neg_cases` the only
    members whose negation is also a member are the set-free ones — where the
    reading is truth in `ℕ`, and one of `φ`, `∼φ` is true — and the two atoms
    `n̄ ∈ X`, `n̄ ∉ X`, whose readings `Small δ n` and `¬ Small γ n` are dual as
    soon as `γ ≤ δ`.  The remaining six shapes are impossible, which is exactly
    what the six `not_inCe₂_*` lemmas of `LowerClass₂.lean` say.

  * **`all₂` and `exs₂` are vacuous.**  Their conclusions have a `∀²`/`∃²` head
    and no member of the class has one: the class contains no set quantifier.

  Everything else is the first-order proof, line for line.
-/
import OrdinalAnalysis.ACAOmega.LowerClass₂

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O] {C : CodedOrder₂ O}

/-! ### The reading of a code -/

/-- The ordinal coded by `n`, if any, is below `δ`. -/
def Small (C : CodedOrder₂ O) (δ : O) (n : ℕ) : Prop := ∀ o : O, C.code o = n → o < δ

/-- Every `≺`-predecessor of `n` is small. -/
def PredsSmall (C : CodedOrder₂ O) (δ : O) (n : ℕ) : Prop :=
  ∀ k : ℕ, C.precN k n → Small C δ k

theorem Small.mono {δ δ' : O} {n : ℕ} (h : δ ≤ δ') (hs : Small C δ n) : Small C δ' n :=
  fun o ho => lt_of_lt_of_le (hs o ho) h

theorem PredsSmall.mono {δ δ' : O} {n : ℕ} (h : δ ≤ δ') (hs : PredsSmall C δ n) :
    PredsSmall C δ' n :=
  fun k hk => (hs k hk).mono h

theorem PredsSmall.congr {δ : O} {n n' : ℕ} (hiff : ∀ k, C.precN k n ↔ C.precN k n')
    (hs : PredsSmall C δ n') : PredsSmall C δ n :=
  fun k hk => hs k ((hiff k).mp hk)

/-- A number all of whose predecessors are below `δ` is at most `δ`: linearity. -/
theorem le_of_predsSmall {δ : O} {n : ℕ} (h : PredsSmall C δ n) {o : O}
    (ho : C.code o = n) : o ≤ δ := by
  refine Gentzen.le_of_forall_lt_lt (fun o' ho' => ?_)
  refine h (C.code o') ?_ o' rfl
  rw [← ho]
  exact C.precN_code_of_lt ho'

theorem Small.of_predsSmall {δ : O} {n : ℕ} (h : PredsSmall C δ n) :
    Small C (OrdinalNotation.succ δ) n :=
  fun _ ho => OrdinalNotation.lt_succ_of_le (le_of_predsSmall h ho)

theorem Small.of_predsSmall_lt {δ δ' : O} {n : ℕ} (h : PredsSmall C δ n) (hδ : δ < δ') :
    Small C δ' n :=
  fun _ ho => lt_of_le_of_lt (le_of_predsSmall h ho) hδ

/-! ### The reading of the class -/

/-- The reading of a class member under the bounds `(γ, δ)`; `∼Prog₂` has
none. -/
def Good₂ (C : CodedOrder₂ O) (γ δ : O) (φ : Proposition ℒₒᵣ) : Prop :=
  (SetFree φ ∧ TrueN₂ φ) ∨
  (∃ n, φ = xat n ∧ Small C δ n) ∨
  (∃ n, φ = nxat n ∧ ¬ Small C γ n) ∨
  (∃ n, φ = ev₂ (belowAt₂ C n) ∧ PredsSmall C δ n) ∨
  (∃ n, φ = ev₂ (P₂ C n) ∧ ¬ Small C γ n ∧ PredsSmall C δ n) ∨
  (∃ k n, φ = ev₂ (precOrXat₂ C k n) ∧ (¬ C.precN k n ∨ Small C δ k)) ∨
  (φ = allXat₂ ∧ ∀ o : O, o < δ) ∨
  (φ = ev₂ (TI₂ C.prec) ∧ ∀ o : O, o < δ)

/-- Some member of the sequent is good. -/
def Bound₂ (C : CodedOrder₂ O) (γ δ : O) (Γ : SecondOrder.Sequent ℒₒᵣ) : Prop :=
  ∃ φ ∈ Γ, Good₂ C γ δ φ

variable {γ δ : O} {φ : Proposition ℒₒᵣ}

theorem Good₂.setFree (hx : SetFree φ) (ht : TrueN₂ φ) : Good₂ C γ δ φ := Or.inl ⟨hx, ht⟩

theorem Good₂.xat {n : ℕ} (h : φ = xat n) (hs : Small C δ n) : Good₂ C γ δ φ :=
  Or.inr (Or.inl ⟨n, h, hs⟩)

theorem Good₂.nxat {n : ℕ} (h : φ = nxat n) (hs : ¬ Small C γ n) : Good₂ C γ δ φ :=
  Or.inr (Or.inr (Or.inl ⟨n, h, hs⟩))

theorem Good₂.belowAt {n : ℕ} (h : φ = ev₂ (belowAt₂ C n)) (hp : PredsSmall C δ n) :
    Good₂ C γ δ φ :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h, hp⟩)))

theorem Good₂.pn {n : ℕ} (h : φ = ev₂ (P₂ C n)) (hs : ¬ Small C γ n)
    (hp : PredsSmall C δ n) : Good₂ C γ δ φ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h, hs, hp⟩))))

theorem Good₂.precOrXat {k n : ℕ} (h : φ = ev₂ (precOrXat₂ C k n))
    (hd : ¬ C.precN k n ∨ Small C δ k) : Good₂ C γ δ φ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, n, h, hd⟩)))))

theorem Good₂.allXat (h : φ = allXat₂) (hall : ∀ o : O, o < δ) : Good₂ C γ δ φ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hall⟩))))))

theorem Good₂.ti (h : φ = ev₂ (TI₂ C.prec)) (hall : ∀ o : O, o < δ) : Good₂ C γ δ φ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hall⟩))))))

/-- Lowering `γ` and raising `δ` keeps a reading good. -/
theorem Good₂.mono {γ' δ' : O} (hγ : γ ≤ γ') (hδ : δ ≤ δ') (hg : Good₂ C γ' δ φ) :
    Good₂ C γ δ' φ := by
  rcases hg with h | ⟨n, h, hs⟩ | ⟨n, h, hs⟩ | ⟨n, h, hp⟩ | ⟨n, h, hs, hp⟩ | ⟨k, n, h, hd⟩ |
    ⟨h, hall⟩ | ⟨h, hall⟩
  · exact Or.inl h
  · exact Good₂.xat h (hs.mono hδ)
  · exact Good₂.nxat h (fun hs' => hs (hs'.mono hγ))
  · exact Good₂.belowAt h (hp.mono hδ)
  · exact Good₂.pn h (fun hs' => hs (hs'.mono hγ)) (hp.mono hδ)
  · exact Good₂.precOrXat h (hd.imp id (fun hs => hs.mono hδ))
  · exact Good₂.allXat h (fun o => lt_of_lt_of_le (hall o) hδ)
  · exact Good₂.ti h (fun o => lt_of_lt_of_le (hall o) hδ)

theorem Bound₂.mono {γ' δ' : O} {Γ : SecondOrder.Sequent ℒₒᵣ} (hγ : γ ≤ γ') (hδ : δ ≤ δ')
    (hb : Bound₂ C γ' δ Γ) : Bound₂ C γ δ' Γ :=
  let ⟨ψ, hψ, hg⟩ := hb
  ⟨ψ, hψ, hg.mono hγ hδ⟩

theorem Bound₂.subset {Γ Γ' : SecondOrder.Sequent ℒₒᵣ} (h : Γ ⊆ Γ')
    (hb : Bound₂ C γ δ Γ) : Bound₂ C γ δ Γ' :=
  let ⟨ψ, hψ, hg⟩ := hb
  ⟨ψ, h hψ, hg⟩

theorem Bound₂_cons {Γ : SecondOrder.Sequent ℒₒᵣ} :
    Bound₂ C γ δ (φ :: Γ) ↔ Good₂ C γ δ φ ∨ Bound₂ C γ δ Γ := by
  simp only [Bound₂, List.exists_mem_cons_iff]

theorem Bound₂.head (hg : Good₂ C γ δ φ) (Γ : SecondOrder.Sequent ℒₒᵣ) :
    Bound₂ C γ δ (φ :: Γ) := Bound₂_cons.mpr (Or.inl hg)

theorem Bound₂.tail {Γ : SecondOrder.Sequent ℒₒᵣ} (hb : Bound₂ C γ δ Γ) :
    Bound₂ C γ δ (φ :: Γ) := Bound₂_cons.mpr (Or.inr hb)

/-! ### Which reading applies to which shape -/

theorem ev₂_belowAt₂_ne_allXat₂ (n : ℕ) : ev₂ (belowAt₂ C n) ≠ allXat₂ := by
  intro h
  rw [ev₂_belowAt₂_eq, allXat₂_eq] at h
  exact absurd (congrArg head₂ (Semiformula.all₁_inj.mp h)) (by simp)

theorem ev₂_precOrXat₂_ne_ev₂_TI₂ (k n : ℕ) :
    ev₂ (precOrXat₂ C k n) ≠ ev₂ (TI₂ C.prec) := by
  intro h
  rw [ev₂_precOrXat₂_eq, ev₂_TI₂_eq] at h
  exact absurd (congrArg head₂ (Semiformula.or_inj.mp h).2) (by simp)

theorem Good₂_setFree_iff (hx : SetFree φ) : Good₂ C γ δ φ ↔ TrueN₂ φ := by
  constructor
  · rintro (h | ⟨n, h, -⟩ | ⟨n, h, -⟩ | ⟨n, h, -⟩ | ⟨n, h, -⟩ | ⟨k, n, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact h.2
    · subst h; exact absurd hx (by simp)
    · subst h; exact absurd hx (by simp)
    · subst h; exact absurd hx (by simp)
    · subst h; exact absurd hx (by simp)
    · subst h; exact absurd hx (by simp)
    · subst h; exact absurd hx (by simp)
    · subst h; exact absurd hx (by simp)
  · exact fun ht => Good₂.setFree hx ht

theorem Good₂_xat_iff (n : ℕ) : Good₂ C γ δ (xat n) ↔ Small C δ n := by
  constructor
  · rintro (h | ⟨m, h, hs⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd h.1 (by simp)
    · rw [xat_inj.mp h]; exact hs
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
  · exact fun hs => Good₂.xat rfl hs

theorem Good₂_nxat_iff (n : ℕ) : Good₂ C γ δ (nxat n) ↔ ¬ Small C γ n := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, hs⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd h.1 (by simp)
    · exact absurd h (ne_of_head₂ (by simp))
    · rw [nxat_inj.mp h]; exact hs
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
  · exact fun hs => Good₂.nxat rfl hs

theorem Good₂_belowAt₂_iff (n : ℕ) :
    Good₂ C γ δ (ev₂ (belowAt₂ C n)) ↔ PredsSmall C δ n := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, hp⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd h.1 (by simp)
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact hp.congr (ev₂_belowAt₂_precN_iff h)
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ev₂_belowAt₂_ne_allXat₂ n)
    · exact absurd h (ne_of_head₂ (by simp))
  · exact fun hp => Good₂.belowAt rfl hp

theorem Good₂_P₂_iff (n : ℕ) :
    Good₂ C γ δ (ev₂ (P₂ C n)) ↔ ¬ Small C γ n ∧ PredsSmall C δ n := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, hs, hp⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ |
      ⟨h, -⟩)
    · exact absurd h.1 (by simp)
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · rw [ev₂_P₂_inj h]; exact ⟨hs, hp⟩
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
  · exact fun ⟨hs, hp⟩ => Good₂.pn rfl hs hp

theorem Good₂_precOrXat₂_iff (k n : ℕ) :
    Good₂ C γ δ (ev₂ (precOrXat₂ C k n)) ↔ (¬ C.precN k n ∨ Small C δ k) := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k', m, h, hd⟩ | ⟨h, -⟩ |
      ⟨h, -⟩)
    · exact absurd h.1 (by simp)
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · obtain ⟨rfl, hiff⟩ := ev₂_precOrXat₂_inj h
      exact hd.imp (fun hn hk => hn (hiff.mp hk)) id
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ev₂_precOrXat₂_ne_ev₂_TI₂ k n)
  · exact fun hd => Good₂.precOrXat rfl hd

theorem Good₂_allXat₂_iff : Good₂ C γ δ allXat₂ ↔ ∀ o : O, o < δ := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨-, hall⟩ |
      ⟨h, -⟩)
    · exact absurd h.1 (by simp)
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h.symm (ev₂_belowAt₂_ne_allXat₂ m)
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact hall
    · exact absurd h (ne_of_head₂ (by simp))
  · exact fun hall => Good₂.allXat rfl hall

theorem Good₂_TI₂_iff : Good₂ C γ δ (ev₂ (TI₂ C.prec)) ↔ ∀ o : O, o < δ := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ |
      ⟨-, hall⟩)
    · exact absurd h.1 (by simp)
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h (ne_of_head₂ (by simp))
    · exact absurd h.symm (ev₂_precOrXat₂_ne_ev₂_TI₂ k m)
    · exact absurd h (ne_of_head₂ (by simp))
    · exact hall
  · exact fun hall => Good₂.ti rfl hall

theorem not_good₂_negProg : ¬ Good₂ C γ δ (ev₂ (∼(Prog₂ C.prec))) := by
  rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
  · exact absurd h.1 (by simp)
  · exact absurd h (ne_of_head₂ (by simp))
  · exact absurd h (ne_of_head₂ (by simp))
  · exact absurd h (ne_of_head₂ (by simp))
  · exact absurd h (ne_of_head₂ (by simp))
  · exact absurd h (ne_of_head₂ (by simp))
  · exact absurd h (ne_of_head₂ (by simp))
  · exact absurd h (ne_of_head₂ (by simp))

/-! ### General identity

The new case.  A member of the class whose negation is also a member is either
set-free — and then one of the two is true in `ℕ` — or one of the two atoms,
whose readings are dual as soon as `γ ≤ δ`. -/

theorem good₂_or_good₂_neg (hle : γ ≤ δ) (h : InCe₂ C φ) (hn : InCe₂ C (∼φ)) :
    Good₂ C γ δ φ ∨ Good₂ C γ δ (∼φ) := by
  rcases h.neg_cases hn with hx | ⟨n, rfl⟩ | ⟨n, rfl⟩
  · by_cases ht : TrueN₂ φ
    · exact Or.inl (Good₂.setFree hx ht)
    · exact Or.inr (Good₂.setFree ((setFree_neg φ).mpr hx) ((trueN₂_neg φ).mpr ht))
  · by_cases hs : Small C γ n
    · exact Or.inl (Good₂.xat rfl (hs.mono hle))
    · exact Or.inr (Good₂.nxat (neg_xat n) hs)
  · by_cases hs : Small C γ n
    · exact Or.inr (Good₂.xat (neg_nxat n) (hs.mono hle))
    · exact Or.inl (Good₂.nxat rfl hs)

/-! ### The lemma -/

set_option maxHeartbeats 2000000 in
/-- **Boundedness.**  A cut-free derivation of height `α` of a sequent in the
class has, for every lower bound `γ`, a good member under `(γ, γ ⊕ ω^α)`. -/
theorem boundedness₂ {α : O} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (h : OmegaDerivable₂ trueArithLits₂ evInst₂ 0 α Γ) :
    InCeSeq₂ C Γ →
      ∀ γ : O, Bound₂ C γ (OrdinalNotation.nadd γ (OrdinalNotation.omegaPow α)) Γ := by
  induction h with
  | @atom α φ hφ =>
      intro _ γ
      exact Bound₂.head (Good₂.setFree (setFree_of_isArithLit₂ hφ.1) hφ.2.1) _
  | @identity α φ =>
      intro hC γ
      have hle : γ ≤ OrdinalNotation.nadd γ (OrdinalNotation.omegaPow α) :=
        OrdinalNotation.le_nadd_left _ _
      have h1 : InCe₂ C φ := hC _ List.mem_cons_self
      have h2 : InCe₂ C (∼φ) := hC _ (List.mem_cons_of_mem _ List.mem_cons_self)
      rcases good₂_or_good₂_neg hle h1 h2 with hg | hg
      · exact Bound₂.head hg _
      · exact Bound₂.tail (Bound₂.head hg _)
  | verum =>
      intro _ γ
      exact Bound₂.head (Good₂.setFree setFree_verum trueN₂_verum) _
  | @or α β φ ψ Γ' hlt _ ih =>
      intro hC γ
      have hle := Gentzen.Boundedness.nadd_omegaPow_le (γ := γ) hlt
      have hB := ih (InCeSeq₂.of_or hC) γ
      rw [Bound₂_cons, Bound₂_cons] at hB
      rcases InCe₂.or_cases (hC _ List.mem_cons_self) with hx | ⟨hφ, hψ⟩ | ⟨k, n, hφ, hψ⟩
      · have hxφ : SetFree φ := ((setFree_or _ _).mp hx).1
        have hxψ : SetFree ψ := ((setFree_or _ _).mp hx).2
        rcases hB with hg | hg | hB
        · exact Bound₂.head (Good₂.setFree hx ((trueN₂_or φ ψ).mpr
            (Or.inl ((Good₂_setFree_iff hxφ).mp hg)))) _
        · exact Bound₂.head (Good₂.setFree hx ((trueN₂_or φ ψ).mpr
            (Or.inr ((Good₂_setFree_iff hxψ).mp hg)))) _
        · exact Bound₂.tail (hB.mono le_rfl hle)
      · subst hφ; subst hψ
        rcases hB with hg | hg | hB
        · exact absurd hg not_good₂_negProg
        · exact Bound₂.head (Good₂.ti ev₂_TI₂_eq.symm
            (fun o => lt_of_lt_of_le (Good₂_allXat₂_iff.mp hg o) hle)) _
        · exact Bound₂.tail (hB.mono le_rfl hle)
      · subst hφ; subst hψ
        rcases hB with hg | hg | hB
        · have ht := (Good₂_setFree_iff (setFree_ev₂_neg_precAt (numAt k) (numAt n))).mp hg
          exact Bound₂.head (Good₂.precOrXat (ev₂_precOrXat₂_eq k n).symm
            (Or.inl ((trueN₂_ev₂_neg_precAt k n).mp ht))) _
        · exact Bound₂.head (Good₂.precOrXat (ev₂_precOrXat₂_eq k n).symm
            (Or.inr (((Good₂_xat_iff k).mp hg).mono hle))) _
        · exact Bound₂.tail (hB.mono le_rfl hle)
  | @and α β₁ β₂ φ ψ Γ' hb hc _ _ ihp ihq =>
      intro hC γ
      have hle₁ := Gentzen.Boundedness.nadd_omegaPow_le (γ := γ) hb
      have hle₂ := Gentzen.Boundedness.nadd_omegaPow_le (γ := γ) hc
      obtain ⟨hCφ, hCψ⟩ := InCeSeq₂.of_and hC
      have hBp := ihp hCφ γ
      have hBq := ihq hCψ γ
      rw [Bound₂_cons] at hBp hBq
      rcases InCe₂.and_cases (hC _ List.mem_cons_self) with hx | ⟨n, hφ, hψ⟩
      · have hxφ : SetFree φ := ((setFree_and _ _).mp hx).1
        have hxψ : SetFree ψ := ((setFree_and _ _).mp hx).2
        rcases hBp with hg | hB
        · rcases hBq with hg' | hB'
          · exact Bound₂.head (Good₂.setFree hx ((trueN₂_and φ ψ).mpr
              ⟨(Good₂_setFree_iff hxφ).mp hg, (Good₂_setFree_iff hxψ).mp hg'⟩)) _
          · exact Bound₂.tail (hB'.mono le_rfl hle₂)
        · exact Bound₂.tail (hB.mono le_rfl hle₁)
      · subst hφ; subst hψ
        rcases hBp with hg | hB
        · rcases hBq with hg' | hB'
          · exact Bound₂.head (Good₂.pn (ev₂_P₂_eq n).symm ((Good₂_nxat_iff n).mp hg')
              (((Good₂_belowAt₂_iff n).mp hg).mono hle₁)) _
          · exact Bound₂.tail (hB'.mono le_rfl hle₂)
        · exact Bound₂.tail (hB.mono le_rfl hle₁)
  | @omegaRule α φ Γ' f hf _ ih =>
      intro hC γ
      have hle : ∀ m, OrdinalNotation.nadd γ (OrdinalNotation.omegaPow (f m))
          ≤ OrdinalNotation.nadd γ (OrdinalNotation.omegaPow α) :=
        fun m => Gentzen.Boundedness.nadd_omegaPow_le (hf m)
      by_cases hctx : ∃ m, Bound₂ C γ (OrdinalNotation.nadd γ
          (OrdinalNotation.omegaPow (f m))) Γ'
      · obtain ⟨m, hB⟩ := hctx
        exact Bound₂.tail (hB.mono le_rfl (hle m))
      · have hno : ∀ m, ¬ Bound₂ C γ (OrdinalNotation.nadd γ
            (OrdinalNotation.omegaPow (f m))) Γ' := fun m hB => hctx ⟨m, hB⟩
        have hprem : ∀ m, Good₂ C γ (OrdinalNotation.nadd γ
            (OrdinalNotation.omegaPow (f m))) (evInst₂.inst φ m) := by
          intro m
          have hB := ih m (InCeSeq₂.of_all hC m) γ
          rw [Bound₂_cons] at hB
          exact hB.resolve_right (hno m)
        rcases InCe₂.all_cases (hC _ List.mem_cons_self) with hx | hφ | ⟨n, hφ⟩
        · refine Bound₂.head (Good₂.setFree hx ((trueN₂_all φ).mpr (fun m => ?_))) _
          exact (trueN₂_inst φ m).mp
            ((Good₂_setFree_iff (setFree_inst ((setFree_all₁ _).mp hx) m)).mp (hprem m))
        · subst hφ
          refine Bound₂.head (Good₂.allXat allXat₂_eq.symm (fun o => ?_)) _
          have hg := hprem (C.code o)
          rw [inst_allXat₂_body] at hg
          exact lt_of_lt_of_le ((Good₂_xat_iff _).mp hg o rfl) (hle _)
        · subst hφ
          refine Bound₂.head (Good₂.belowAt (ev₂_belowAt₂_eq n).symm (fun k hk => ?_)) _
          have hg := hprem k
          rw [inst_belowBody₂] at hg
          exact (((Good₂_precOrXat₂_iff k n).mp hg).resolve_left (not_not.mpr hk)).mono (hle k)
  | @exs α β φ Γ' m hlt _ ih =>
      intro hC γ
      have hle := Gentzen.Boundedness.nadd_omegaPow_le (γ := γ) hlt
      have hC' := InCeSeq₂.of_exs hC m
      rcases InCe₂.exs_cases (hC _ List.mem_cons_self) with hx | hφ
      · have hB := ih hC' γ
        rw [Bound₂_cons] at hB
        rcases hB with hg | hB
        · refine Bound₂.head (Good₂.setFree hx ((trueN₂_exs φ).mpr ⟨m, ?_⟩)) _
          exact (trueN₂_inst φ m).mp
            ((Good₂_setFree_iff (setFree_inst ((setFree_exs₁ _).mp hx) m)).mp hg)
        · exact Bound₂.tail (hB.mono le_rfl hle)
      · subst hφ
        have hB := ih hC' γ
        rw [inst_negProg₂_body, Bound₂_cons] at hB
        rcases hB with hg | hB
        · obtain ⟨-, hp⟩ := (Good₂_P₂_iff m).mp hg
          -- invoke the hypothesis again, above the counterexample
          have hB' := ih hC' (OrdinalNotation.succ (OrdinalNotation.nadd γ
            (OrdinalNotation.omegaPow β)))
          rw [inst_negProg₂_body, Bound₂_cons] at hB'
          rcases hB' with hg' | hB'
          · exact absurd (Small.of_predsSmall hp) ((Good₂_P₂_iff m).mp hg').1
          · refine Bound₂.tail (hB'.mono ?_ (Gentzen.Boundedness.bump_le hlt))
            exact le_trans (OrdinalNotation.le_nadd_left _ _) (OrdinalNotation.le_succ _)
        · exact Bound₂.tail (hB.mono le_rfl hle)
  | @all₂ α β φ Γ' _ _ _ =>
      intro hC _
      exact (InCe₂.not_all₂ (hC _ List.mem_cons_self)).elim
  | @exs₂ α β φ ψ Γ' _ _ _ _ =>
      intro hC _
      exact (InCe₂.not_exs₂ (hC _ List.mem_cons_self)).elim
  | contraction ss _ ih =>
      intro hC γ
      exact (ih (InCeSeq₂.of_subset hC ss) γ).subset ss
  | cut hc _ _ _ _ _ _ =>
      exact absurd hc (not_lt.mpr (NONote.zero_le' _))

/-- **`TI₂(≺, X)` has no cut-free derivation at any height.** -/
theorem not_derivable_TI₂ (C : CodedOrder₂ O) (α : O) :
    ¬ OmegaDerivable₂ trueArithLits₂ evInst₂ 0 α [ev₂ (TI₂ C.prec)] := by
  intro h
  have hB := boundedness₂ h (fun ψ hψ => by
    simp only [List.mem_singleton] at hψ
    subst hψ
    exact InCe₂.ti) α
  rw [Bound₂_cons] at hB
  rcases hB with hg | ⟨ψ, hψ, -⟩
  · exact lt_irrefl _ (Good₂_TI₂_iff.mp hg _)
  · simp at hψ

/-- **The `ε_a`-segment instance.**  Transfinite induction along the coded
Veblen ordering restricted to the notations below `ε_a` has no cut-free
`ACA_∞`-derivation at any height in that segment. -/
theorem not_derivable_TI₂_epsilonSeg (a : Gamma0Note) (α : Gamma0Note.EpsilonBelow a) :
    ¬ OmegaDerivable₂ trueArithLits₂ evInst₂ 0 α
        [ev₂ (TI₂ (epsilonSegOrder₂ a).prec)] :=
  not_derivable_TI₂ (epsilonSegOrder₂ a) α

end OrdinalAnalysis.ACAOmega
