/-
  The domain lemma of the collapsing theorem, and the adjudication of the two hull designs.

  **The domain lemma (true, for the level-free operator of `HullSingle.lean`).**
  `dom_add_omegaPow`: `HullHypS k α X`, `α ∈ H_α(X)` and `β ∈ H_α(X)` give
  `Dom (ϑ_k (α + ω^β))`, with no bound `α, β ≺ Ω_{k+1}`.  The heights of the collapsing theorem
  (Buchholz 1992, Theorem 4.8; Freund, arXiv:2204.09321, Theorem 6.7) are exactly of this shape,
  far above `Ω_{k+1}`.  The proof: `G_le_of_mem_HopS` (every `G_k`-argument of a member of
  `H_α(X)` is `≼ α`): if some `G_k`-argument of `x` exceeded `α`, its largest one `μ` would be a
  domain point of `ϑ_k` (`dom_theta_of_max_G`), so `x ∈ C(μ, ϑ_k μ)` by the hull hypothesis, and
  every `G_k`-argument of a member of `C(μ, ϑ_k μ)` is `≺ μ` (`CsetS.G_lt`) — so `μ ≺ μ`.
  Corollary: `theta_add_omegaPow_mem_HopS` without the `≺ Ω_{k+1}` hypotheses.
  `HullHypGe k` (the hypothesis at every level `≥ k`) passes upward by definition and keeps
  `mono`, `lt_theta`, `union_singleton` and the domain lemma (`dom_add_omegaPow_ge`).

  **The same statement is false for the merged per-level operators `Hop k` of `Hull.lean`**
  (`not_dom_add_omegaPow_Hop`, and for every index at once `exists_mem_Hop_not_dom`): the clause
  `CsetT.ofThetaHigh` admits `ϑ_j ξ`, `j > k`, with no bound on `ξ`, so `Hop k α X` contains
  terms with arbitrarily large `G_k`-arguments.  The merged operators also do not form one
  family across levels: `Hop 0 0 ∅` and `Hop 1 0 ∅` are incomparable
  (`not_Hop_zero_subset_Hop_one`, `not_Hop_one_subset_Hop_zero`), and `Hop 1 0` is not nice at
  level `0` (`not_nice_zero_Hop_one`).

  **The level-free design's minimality holds** (`HullSingle.theta_isLeastS`).  The concrete term
  offered against it, `ϑ_0(Ω_100)` (Lean `theta 0 (Omega 99)`), does lie below every `ϑ_6 α`
  (`theta0_Omega99_lt_theta6`), and it lies in every candidate hull of Proposition 3.9 at
  level 6 through the clause `γ ≺ β` (`theta0_Omega99_mem_of_candidate`).  The term offered
  against the domain lemma, `α = ϑ_5(Ω_10)` (Lean `theta 5 (Omega 9)`), satisfies its
  hypotheses for the merged `Hop 3` (`hA_mem_Hop_three`, `not_dom_theta_three_hA_succ`) but not
  for the level-free operator (`hA_not_mem_HopS`).
-/
import OrdinalAnalysis.Ordinal.ThetaW.HullSingle

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

/-- `G_k` is transitive: the `G_k`-arguments of a `G_k`-argument of `α` are `G_k`-arguments of
`α`. -/
theorem G_subset_of_mem_G {k : ℕ} : ∀ {a x : ThetaWTerm}, x ∈ G k a → ∀ y ∈ G k x, y ∈ G k a
  | Omega _, x, h => by simp at h
  | theta j a, x, h => by
    by_cases hj : k < j
    · rw [G_theta_of_lt hj] at h ⊢
      intro y hy
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_of_mem _ hy
      · exact List.mem_cons_of_mem _ (G_subset_of_mem_G h y hy)
    · rw [G_theta_of_le (Nat.le_of_not_lt hj)] at h; simp at h
  | sum xs, x, h => by
    obtain ⟨z, hz, hx⟩ := mem_G_sum.mp h
    intro y hy
    exact mem_G_sum.mpr ⟨z, hz, G_subset_of_mem_G hx y hy⟩
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hz

/-- A non-empty list of terms has a largest entry. -/
theorem exists_max_mem : ∀ {L : List ThetaWTerm}, L ≠ [] → ∃ m ∈ L, ∀ z ∈ L, z ≤ m
  | [], h => absurd rfl h
  | [x], _ => ⟨x, List.mem_singleton_self x, fun z hz => (List.mem_singleton.mp hz) ▸ le_refl' x⟩
  | x :: y :: ys, _ => by
    obtain ⟨m, hm, hmax⟩ := exists_max_mem (L := y :: ys) (List.cons_ne_nil y ys)
    rcases le_total' x m with hxm | hmx
    · refine ⟨m, List.mem_cons_of_mem x hm, fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hxm
      · exact hmax z hz
    · refine ⟨x, List.mem_cons_self, fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact le_refl' z
      · exact le_trans' (hmax z hz) hmx

/-- The largest `G_k`-argument `μ` of a domain term is a domain point of `ϑ_k`: its own
`G_k`-arguments are `G_k`-arguments of the term, hence `≼ μ`, and shorter than `μ`. -/
theorem dom_theta_of_max_G {k : ℕ} {x m : ThetaWTerm} (hx : Dom x) (hm : m ∈ G k x)
    (hmax : ∀ z ∈ G k x, z ≤ m) : Dom (theta k m) :=
  (dom_theta_iff k m).mpr ⟨hx.of_mem_G hm, fun z hz => by
    rcases (le_def.mp (hmax z (G_subset_of_mem_G hm z hz))) with h | rfl
    · exact h
    · exact absurd (l_lt_of_mem_G hz) (Nat.lt_irrefl _)⟩

end ThetaWTerm

namespace ThetaWNoteD

open ThetaWTerm

/-! ### The domain lemma for the level-free operator -/

/-- **Every `G_k`-argument of a member of `H_α(X)` is `≼ α`**, under the level-`k` hull
hypothesis. -/
theorem G_le_of_mem_HopS {k : ℕ} {a x : ThetaWNoteD} {X : Set ThetaWNoteD}
    (hX : HullHypS k a X) (hx : x ∈ HopS a X) : ∀ y ∈ G k x.1, y ≤ a.1 := by
  intro y hy
  by_contra hya
  have hay : a.1 < y := ThetaWTerm.not_le_iff_lt hya
  obtain ⟨m, hm, hmax⟩ := exists_max_mem (List.ne_nil_of_mem hy)
  have hdm : Dom (ThetaWTerm.theta k m) := dom_theta_of_max_G x.2.2 hm hmax
  let c : ThetaWNoteD := ⟨m, x.2.1.of_mem_G hm, x.2.2.of_mem_G hm⟩
  have hac : a < c := show a.1 < m from lt_of_lt_of_le' hay (hmax y hy)
  have hxC : x ∈ CsetS c (thetaD k c hdm) := hX.HopS_subset hac hdm hx
  have hmm : m < m :=
    ThetaWTerm.CsetS.G_lt k hxC x.2.1 (le_of_lt' (theta_lt_Omega_self k m)) m hm
  exact lt_irrefl' m hmm

/-- `G_k(α + ω^β) ⊆ G_k(α) ∪ G_k(β)`. -/
theorem mem_G_add_omegaPow {k : ℕ} {a b : ThetaWNoteD} {y : ThetaWTerm}
    (hy : y ∈ G k (a + omegaPow b).1) : y ∈ G k a.1 ∨ y ∈ G k b.1 := by
  have h1 : (a + omegaPow b).1 = ofList (a + omegaPow b).entries :=
    (ofList_toList (a + omegaPow b).2.1).symm
  rw [h1, entries_add, entries_omegaPow, mem_G_ofList] at hy
  obtain ⟨z, hz, hyz⟩ := hy
  rcases mem_addL hz with hz | hz
  · left
    rw [← ofList_toList a.2.1, mem_G_ofList]
    exact ⟨z, hz, hyz⟩
  · right
    rw [List.mem_singleton.mp hz] at hyz
    exact hyz

/-- The domain lemma, weakest form: `ϑ_k (α + ω^β)` is in the domain as soon as the
`G_k`-arguments of `α` and `β` are `≼ α`. -/
theorem dom_add_omegaPow_of_G_le {k : ℕ} {a b : ThetaWNoteD} (ha : ∀ y ∈ G k a.1, y ≤ a.1)
    (hb : ∀ y ∈ G k b.1, y ≤ a.1) : Dom (ThetaWTerm.theta k (a + omegaPow b).1) :=
  (dom_theta_iff _ _).mpr ⟨(a + omegaPow b).2.2, fun y hy =>
    lt_of_le_of_lt' ((mem_G_add_omegaPow hy).elim (ha y) (hb y)) (lt_add_omegaPow_hull a b)⟩

/-- **The domain lemma of the collapsing theorem** (the audit's statement, verbatim, for the
level-free operator): `HullHypS k α X`, `α, β ∈ H_α(X)` give `Dom (ϑ_k (α + ω^β))`. -/
theorem dom_add_omegaPow {k : ℕ} {a b : ThetaWNoteD} {X : Set ThetaWNoteD}
    (hX : HullHypS k a X) (ha : a ∈ HopS a X) (hb : b ∈ HopS a X) :
    Dom (ThetaWTerm.theta k (a + omegaPow b).1) :=
  dom_add_omegaPow_of_G_le (G_le_of_mem_HopS hX ha) (G_le_of_mem_HopS hX hb)

/-- `α, β ∈ H_α(X)` give `α + ω^β ∈ H_{α + ω^β}(X)`. -/
theorem add_omegaPow_mem_HopS {a b : ThetaWNoteD} {X : Set ThetaWNoteD}
    (ha : a ∈ HopS a X) (hb : b ∈ HopS a X) : a + omegaPow b ∈ HopS (a + omegaPow b) X :=
  HopS_subset_HopS (lt_add_omegaPow_hull a b) X
    ((HopS_nice a).add_mem ha ((HopS_nice a).omegaPow_mem hb))

/-- **Theorem 6.7's membership fact, with no `≺ Ω_{k+1}` bound**: `HullHypS k α X` and
`α, β ∈ H_α(X)` give `ϑ_k (α + ω^β) ∈ H_{α + ω^β}(X)`. -/
theorem theta_add_omegaPow_mem_HopS {k : ℕ} {a b : ThetaWNoteD} {X : Set ThetaWNoteD}
    (hX : HullHypS k a X) (ha : a ∈ HopS a X) (hb : b ∈ HopS a X) :
    thetaD k (a + omegaPow b) (dom_add_omegaPow hX ha hb) ∈ HopS (a + omegaPow b) X :=
  theta_mem_HopS k (add_omegaPow_mem_HopS ha hb) le_rfl (dom_add_omegaPow hX ha hb)

/-! ### The hull hypothesis at all levels `≥ k` (Buchholz's `𝒜(Θ; γ, κ, μ)` quantifies over
every `τ ⪰ κ`); it passes upward by definition and keeps every property used above -/

/-- `HullHypS j α X` for every level `j ≥ k`. -/
def HullHypGe (k : ℕ) (a : ThetaWNoteD) (X : Set ThetaWNoteD) : Prop :=
  ∀ j, k ≤ j → HullHypS j a X

theorem HullHypGe.hullHypS {k : ℕ} {a : ThetaWNoteD} {X : Set ThetaWNoteD}
    (h : HullHypGe k a X) : HullHypS k a X := h k le_rfl

theorem HullHypGe.up {k j : ℕ} {a : ThetaWNoteD} {X : Set ThetaWNoteD} (h : HullHypGe k a X)
    (hkj : k ≤ j) : HullHypGe j a X :=
  fun i hji => h i (le_trans hkj hji)

theorem HullHypGe.mono {k : ℕ} {a b : ThetaWNoteD} {X : Set ThetaWNoteD} (h : HullHypGe k a X)
    (hab : a ≤ b) : HullHypGe k b X :=
  fun j hkj => (h j hkj).mono hab

theorem HullHypGe.lt_theta {k : ℕ} {a c d : ThetaWNoteD} {X : Set ThetaWNoteD}
    (h : HullHypGe k a X) (hac : a < c) (hc : Dom (ThetaWTerm.theta k c.1)) (hd : d ∈ HopS a X)
    (hΩ : d < Omega k) : d < thetaD k c hc :=
  h.hullHypS.lt_theta hac hc hd hΩ

theorem HullHypGe.union_singleton {k : ℕ} {a d g : ThetaWNoteD} {X : Set ThetaWNoteD}
    (h : HullHypGe k a X) (hd : d ∈ HopS a X) (hΩ : d < Omega k) (hgd : g < d) :
    HullHypGe k a (X ∪ {g}) := by
  intro j hkj
  have hkj' : Omega k ≤ Omega j := by
    rcases Nat.lt_or_eq_of_le hkj with h' | rfl
    · exact le_of_lt ((Omega_lt_Omega_iff k j).mpr h')
    · exact le_rfl
  exact (h j hkj).union_singleton hd (lt_of_lt_of_le hΩ hkj') hgd

theorem dom_add_omegaPow_ge {k : ℕ} {a b : ThetaWNoteD} {X : Set ThetaWNoteD}
    (hX : HullHypGe k a X) (ha : a ∈ HopS a X) (hb : b ∈ HopS a X) :
    Dom (ThetaWTerm.theta k (a + omegaPow b).1) :=
  dom_add_omegaPow hX.hullHypS ha hb

/-! ### The merged per-level operators: the domain lemma fails -/

/-- `ϑ_1(Ω_2)` (Lean `theta 1 (Omega 1)`). -/
def tB : ThetaWNoteD := ⟨ThetaWTerm.theta 1 (ThetaWTerm.Omega 1), by simp, dom_theta_Omega 1 1⟩

theorem tB_mem_Hop_zero (a : ThetaWNoteD) (X : Set ThetaWNoteD) : tB ∈ Hop 0 a X :=
  fun _ _ _ _ => CsetT.ofThetaHigh (by omega) (.ofOmega 1)

theorem zero_add_omegaPow_tB : zero + omegaPow tB = tB := by
  rw [zero_add, omegaPow_eq_self_iff.mpr (isPrin_theta 1 _)]

theorem not_dom_theta_zero_tB :
    ¬ Dom (ThetaWTerm.theta 0 (ThetaWTerm.theta 1 (ThetaWTerm.Omega 1))) := by
  intro h
  have hmem : ThetaWTerm.Omega 1 ∈ G 0 (ThetaWTerm.theta 1 (ThetaWTerm.Omega 1)) := by
    rw [G_theta_of_lt (by omega)]; exact List.mem_cons_self
  exact absurd ((Omega_lt_theta_iff 1 1 _).mp (h.G_lt hmem)) (Nat.lt_irrefl 1)

/-- **The audit's `dom_add_omegaPow` is false for the merged operators `Hop k`**
(`k = 0`, `α = 0`, `X = ∅`, `β = ϑ_1(Ω_2)`). -/
theorem not_dom_add_omegaPow_Hop :
    ¬ ∀ (k : ℕ) (a b : ThetaWNoteD) (X : Set ThetaWNoteD), HullHyp k a X → a ∈ Hop k a X →
      b ∈ Hop k a X → Dom (ThetaWTerm.theta k (a + omegaPow b).1) := by
  intro h
  have := h 0 zero tB ∅ (fun _ _ _ => Set.empty_subset _) (Hop_nice 0 zero).zero_mem
    (tB_mem_Hop_zero zero ∅)
  rw [zero_add_omegaPow_tB] at this
  exact not_dom_theta_zero_tB this

/-- `β ∈ G_k(α + ω^β)` when `β = ϑ_j ξ` with `j > k`: `ξ` is a `G_k`-argument of `α + ω^β`. -/
theorem mem_G_add_omegaPow_right {k : ℕ} (a b : ThetaWNoteD) {y : ThetaWTerm}
    (hy : y ∈ G k b.1) : y ∈ G k (a + omegaPow b).1 := by
  rw [← ofList_toList (a + omegaPow b).2.1]
  change y ∈ G k (ofList (a + omegaPow b).entries)
  rw [entries_add, entries_omegaPow, mem_G_ofList]
  refine ⟨b.1, ?_, hy⟩
  rw [addL_cons]
  exact List.mem_append_right _ List.mem_cons_self

/-- For **every** level, index and `X`, the merged `Hop k α X` contains a `β` with
`ϑ_k (α + ω^β)` outside the domain: `β = ϑ_{k+1}(Ω_N)` with `Ω_N` above `α`. -/
theorem exists_mem_Hop_not_dom (k : ℕ) (a : ThetaWNoteD) (X : Set ThetaWNoteD) :
    ∃ b ∈ Hop k a X, ¬ Dom (ThetaWTerm.theta k (a + omegaPow b).1) := by
  obtain ⟨n, hn⟩ := exists_levLT a.1
  have haN : a < Omega (n + k + 1) := by
    have h1 : a.1 < ThetaWTerm.Omega n := lt_Omega_of_levLT hn
    have h2 : ThetaWTerm.Omega n < ThetaWTerm.Omega (n + k + 1) :=
      (Omega_lt_Omega_iff n _).mpr (by omega)
    exact lt_trans' h1 h2
  let b : ThetaWNoteD := ⟨ThetaWTerm.theta (k + 1) (ThetaWTerm.Omega (n + k + 1)), by simp,
    dom_theta_Omega (k + 1) (n + k + 1)⟩
  have hbN : b < Omega (n + k + 1) :=
    show ThetaWTerm.theta (k + 1) _ < ThetaWTerm.Omega (n + k + 1) from
      (theta_lt_Omega_iff _ _ _).mpr (by omega)
  refine ⟨b, fun _ _ _ _ => CsetT.ofThetaHigh (by omega) (.ofOmega _), fun h => ?_⟩
  have hmem : ThetaWTerm.Omega (n + k + 1) ∈ G k (a + omegaPow b).1 :=
    mem_G_add_omegaPow_right a b
      (by rw [G_theta_of_lt (show k < k + 1 by omega)]; exact List.mem_cons_self)
  have hlt : a + omegaPow b < Omega (n + k + 1) := add_lt_Omega haN (omegaPow_lt_Omega hbN)
  exact lt_asymm' (h.G_lt hmem) hlt

/-! ### The paper counterexample `α = ϑ_5(Ω_10)`, `k = 3`, `β = 0`, against both hulls -/

/-- `ϑ_5(Ω_10)` (Lean `theta 5 (Omega 9)`). -/
def hA : ThetaWNoteD := ⟨ThetaWTerm.theta 5 (ThetaWTerm.Omega 9), by simp, dom_theta_Omega 5 9⟩

/-- For the merged `Hop 3` the hypothesis `α ∈ H_α(∅)` holds (clause `ofThetaHigh`). -/
theorem hA_mem_Hop_three (X : Set ThetaWNoteD) : hA ∈ Hop 3 hA X :=
  fun _ _ _ _ => CsetT.ofThetaHigh (by omega) (.ofOmega 9)

/-- ... and the conclusion fails: `ϑ_3 (α + ω^0)` is not in the domain. -/
theorem not_dom_theta_three_hA_succ : ¬ Dom (ThetaWTerm.theta 3 (hA + omegaPow zero).1) := by
  intro h
  have hmem : ThetaWTerm.Omega 9 ∈ G 3 (hA + omegaPow zero).1 := by
    have h1 : (hA + omegaPow zero).1 = ofList (hA + omegaPow zero).entries :=
      (ofList_toList (hA + omegaPow zero).2.1).symm
    rw [h1, entries_add, entries_omegaPow, mem_G_ofList]
    refine ⟨hA.1, ?_, by
      change ThetaWTerm.Omega 9 ∈ G 3 (ThetaWTerm.theta 5 (ThetaWTerm.Omega 9))
      rw [G_theta_of_lt (by omega)]; exact List.mem_cons_self⟩
    rw [addL_cons]
    refine List.mem_append_left _ (mem_filter_geb.mpr ⟨?_, nil_le _⟩)
    exact List.mem_singleton_self _
  have hlt : hA + omegaPow zero < Omega 9 := by
    refine add_lt_Omega ?_ (omegaPow_lt_Omega ?_)
    · exact show ThetaWTerm.theta 5 _ < ThetaWTerm.Omega 9 from
        (theta_lt_Omega_iff _ _ _).mpr (by omega)
    · exact show ThetaWTerm.sum [] < ThetaWTerm.Omega 9 from nil_lt_prin trivial
  exact lt_asymm' (h.G_lt hmem) hlt

/-- The paper counterexample refutes the audit's lemma for the merged `Hop 3`. -/
theorem hA_refutes_Hop :
    HullHyp 3 hA ∅ ∧ hA ∈ Hop 3 hA ∅ ∧ zero ∈ Hop 3 hA ∅ ∧
      ¬ Dom (ThetaWTerm.theta 3 (hA + omegaPow zero).1) :=
  ⟨fun _ _ _ => Set.empty_subset _, hA_mem_Hop_three ∅, (Hop_nice 3 hA).zero_mem,
    not_dom_theta_three_hA_succ⟩

/-- For the level-free operator the same term violates the hypothesis `α ∈ H_α(∅)`: its
`G_3`-argument `Ω_10` is not below the index. -/
theorem hA_not_mem_HopS : hA ∉ HopS hA ∅ := by
  intro h
  have hle := G_le_of_mem_HopS (k := 3) (fun _ _ _ => Set.empty_subset _) h (ThetaWTerm.Omega 9)
    (by change ThetaWTerm.Omega 9 ∈ G 3 (ThetaWTerm.theta 5 (ThetaWTerm.Omega 9))
        rw [G_theta_of_lt (by omega)]; exact List.mem_cons_self)
  exact not_le_of_lt' ((theta_lt_Omega_iff 5 9 _).mpr (by omega)) hle

/-! ### The merged operators do not form one family across levels -/

/-- `ϑ_1(Ω_6)` and `ϑ_0(Ω_6)` (Lean `theta 1 (Omega 5)`, `theta 0 (Omega 5)`). -/
def t15 : ThetaWNoteD := ⟨ThetaWTerm.theta 1 (ThetaWTerm.Omega 5), by simp, dom_theta_Omega 1 5⟩
def t05 : ThetaWNoteD := ⟨ThetaWTerm.theta 0 (ThetaWTerm.Omega 5), by simp, dom_theta_Omega 0 5⟩

theorem not_Omega5_lt_one : ¬ ThetaWTerm.Omega 5 < one.1 :=
  lt_asymm' (one_lt_prin (p := Omega 5) trivial)

theorem t15_mem_Hop_zero : t15 ∈ Hop 0 zero ∅ :=
  fun _ _ _ _ => CsetT.ofThetaHigh (by omega) (.ofOmega 5)

theorem t15_not_mem_Hop_one : t15 ∉ Hop 1 zero ∅ := by
  intro h
  have h1 := h one zero zero_lt_one (Set.empty_subset _)
  change CsetT 1 one.1 (ThetaWTerm.sum []) (ThetaWTerm.theta 1 (ThetaWTerm.Omega 5)) at h1
  cases h1 with
  | ofLt h => exact not_lt_nil _ h
  | ofThetaLow hj _ => omega
  | ofThetaHigh hj _ => omega
  | ofThetaOwn _ h2 _ => exact not_Omega5_lt_one h2

theorem t05_mem_Hop_one : t05 ∈ Hop 1 zero ∅ :=
  fun _ _ _ _ => CsetT.ofThetaLow (by omega) _

theorem t05_not_mem_Hop_zero : t05 ∉ Hop 0 zero ∅ := by
  intro h
  have h1 := h one zero zero_lt_one (Set.empty_subset _)
  change CsetT 0 one.1 (ThetaWTerm.sum []) (ThetaWTerm.theta 0 (ThetaWTerm.Omega 5)) at h1
  cases h1 with
  | ofLt h => exact not_lt_nil _ h
  | ofThetaLow hj _ => omega
  | ofThetaHigh hj _ => omega
  | ofThetaOwn _ h2 _ => exact not_Omega5_lt_one h2

theorem not_Hop_zero_subset_Hop_one : ¬ Hop 0 zero ∅ ⊆ Hop 1 zero ∅ :=
  fun h => t15_not_mem_Hop_one (h t15_mem_Hop_zero)

theorem not_Hop_one_subset_Hop_zero : ¬ Hop 1 zero ∅ ⊆ Hop 0 zero ∅ :=
  fun h => t05_not_mem_Hop_zero (h t05_mem_Hop_one)

/-- `H_{1,0}` is not nice at level `0`: `E_0(ϑ_1(Ω_6)) = ∅`, but `ϑ_1(Ω_6) ∉ H_{1,0}(∅)`. -/
theorem not_nice_zero_Hop_one : ¬ Nice 0 (Hop 1 zero) := by
  intro h
  refine t15_not_mem_Hop_one (h.mem_iff.mpr fun g hg => ?_)
  change g.1 ∈ E 0 (ThetaWTerm.theta 1 (ThetaWTerm.Omega 5)) at hg
  rw [E_theta_of_lt (by omega)] at hg
  simp at hg

/-! ### The paper counterexample `ϑ_0(Ω_100) ≺ ϑ_6(α)` against the level-free hull -/

/-- `ϑ_0(Ω_100)` (Lean `theta 0 (Omega 99)`). -/
def t099 : ThetaWNoteD :=
  ⟨ThetaWTerm.theta 0 (ThetaWTerm.Omega 99), by simp, dom_theta_Omega 0 99⟩

/-- The order fact: true, by position. -/
theorem theta0_Omega99_lt_theta6 (a : ThetaWTerm) :
    ThetaWTerm.theta 0 (ThetaWTerm.Omega 99) < ThetaWTerm.theta 6 a :=
  theta_lt_theta_of_lt_level _ _ (by omega)

/-- The claimed consequence fails: `ϑ_0(Ω_100)` lies in `C(α, γ)` for **every** candidate `γ`
of Proposition 3.9 at level 6 (`Ω_6 ∈ C(α, γ) ∩ Ω_7` forces `Ω_6 ≺ γ`, and
`ϑ_0(Ω_100) ≺ Ω_6`), through the clause `γ ≺ β`. -/
theorem theta0_Omega99_mem_of_candidate (a c : ThetaWNoteD)
    (hc : ∀ d ∈ CsetS a c, d < Omega 6 → d < c) : t099 ∈ CsetS a c := by
  have hΩc : Omega 5 < c :=
    hc (Omega 5) (Omega_mem_CsetS 5 a c) ((Omega_lt_Omega_iff 5 6).mpr (by omega))
  exact mem_CsetS_of_lt (lt_trans' ((theta_lt_Omega_iff 0 5 _).mpr (by omega)) hΩc)

/-- In particular `ϑ_0(Ω_100) ∈ C(α, ϑ_6 α)`. -/
theorem theta0_Omega99_mem_CsetS_theta6 (a : ThetaWNoteD)
    (hdom : Dom (ThetaWTerm.theta 6 a.1)) : t099 ∈ CsetS a (thetaD 6 a hdom) :=
  mem_CsetS_of_lt (theta0_Omega99_lt_theta6 a.1)

end ThetaWNoteD

end OrdinalAnalysis
