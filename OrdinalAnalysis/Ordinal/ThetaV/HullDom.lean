/- Source: OrdinalAnalysis\Ordinal\ThetaW\HullDom.lean (mechanical rename ThetaW -> ThetaV via
   mechanical translation, residue by hand: the `OmegaW` arm of `G_subset_of_mem_G`, the one
   exhaustive match on term shape in the part of this file that is ported). Deliberately NOT
   ported: `ThetaW/HullDom.lean`'s second half (from its own `/-! ### The merged per-level
   operators -/` section on: `tB`, `hA`, `t15`, `t05`, `not_dom_add_omegaPow_Hop`,
   `exists_mem_Hop_not_dom`, `not_Hop_zero_subset_Hop_one`, `not_Hop_one_subset_Hop_zero`,
   `not_nice_zero_Hop_one`, `theta0_Omega99_*`). That section is the historical adjudication
   against `ThetaW/Hull.lean`'s rejected per-level design (`Hop`/`CsetT`/`HullHyp`/`Nice`), none of
   which exists in `ThetaV` (the design notes
   §1: `Hull`/`HullCofinal` "not copied") — there is nothing left for those theorems to be about.
   Only the first half (the domain lemma survives for the level-free operator) is ported. -/
/-
  The domain lemma of the collapsing theorem, for the level-free operator of `HullSingle.lean`.

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

  None of this proof touches `OmegaW` directly except through `G_subset_of_mem_G` (`G_k` is
  transitive on raw terms, needed by `dom_theta_of_max_G`): `G k OmegaW = []` (`G_OmegaW`), so its
  `OmegaW` case is vacuous, exactly like every other `G_k`-vanishing case in `HullSingle.lean`.
-/
import OrdinalAnalysis.Ordinal.ThetaV.HullSingle

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaVTerm

/-- `G_k` is transitive: the `G_k`-arguments of a `G_k`-argument of `α` are `G_k`-arguments of
`α`. -/
theorem G_subset_of_mem_G {k : ℕ} : ∀ {a x : ThetaVTerm}, x ∈ G k a → ∀ y ∈ G k x, y ∈ G k a
  | Omega _, x, h => by simp at h
  | OmegaW, x, h => by simp at h
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
theorem exists_max_mem : ∀ {L : List ThetaVTerm}, L ≠ [] → ∃ m ∈ L, ∀ z ∈ L, z ≤ m
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
theorem dom_theta_of_max_G {k : ℕ} {x m : ThetaVTerm} (hx : Dom x) (hm : m ∈ G k x)
    (hmax : ∀ z ∈ G k x, z ≤ m) : Dom (theta k m) :=
  (dom_theta_iff k m).mpr ⟨hx.of_mem_G hm, fun z hz => by
    rcases (le_def.mp (hmax z (G_subset_of_mem_G hm z hz))) with h | rfl
    · exact h
    · exact absurd (l_lt_of_mem_G hz) (Nat.lt_irrefl _)⟩

end ThetaVTerm

namespace ThetaVNoteD

open ThetaVTerm

/-! ### The domain lemma for the level-free operator -/

/-- `α ≺ α + ω(β)`.  Level-independent (`ThetaW/Hull.lean`'s `lt_add_omegaPow_hull`; not in
`ThetaV/Arith.lean` itself, so inlined here by hand, mechanical rename only, same as `thetaD`/
`IsOperator`/`adjoin` in `HullSingle.lean`). -/
theorem lt_add_omegaPow_hull (a b : ThetaVNoteD) : a < a + omegaPow b := by
  have h := add_lt_add_left a (lt_of_lt_of_le zero_lt_one (one_le_omegaPow b))
  rwa [add_zero] at h

/-- **Every `G_k`-argument of a member of `H_α(X)` is `≼ α`**, under the level-`k` hull
hypothesis. -/
theorem G_le_of_mem_HopS {k : ℕ} {a x : ThetaVNoteD} {X : Set ThetaVNoteD}
    (hX : HullHypS k a X) (hx : x ∈ HopS a X) : ∀ y ∈ G k x.1, y ≤ a.1 := by
  intro y hy
  by_contra hya
  have hay : a.1 < y := ThetaVTerm.not_le_iff_lt hya
  obtain ⟨m, hm, hmax⟩ := exists_max_mem (List.ne_nil_of_mem hy)
  have hdm : Dom (ThetaVTerm.theta k m) := dom_theta_of_max_G x.2.2 hm hmax
  let c : ThetaVNoteD := ⟨m, x.2.1.of_mem_G hm, x.2.2.of_mem_G hm⟩
  have hac : a < c := show a.1 < m from lt_of_lt_of_le' hay (hmax y hy)
  have hxC : x ∈ CsetS c (thetaD k c hdm) := hX.HopS_subset hac hdm hx
  have hmm : m < m :=
    ThetaVTerm.CsetS.G_lt k hxC x.2.1 (le_of_lt' (theta_lt_Omega_self k m)) m hm
  exact lt_irrefl' m hmm

/-- `G_k(α + ω^β) ⊆ G_k(α) ∪ G_k(β)`. -/
theorem mem_G_add_omegaPow {k : ℕ} {a b : ThetaVNoteD} {y : ThetaVTerm}
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
theorem dom_add_omegaPow_of_G_le {k : ℕ} {a b : ThetaVNoteD} (ha : ∀ y ∈ G k a.1, y ≤ a.1)
    (hb : ∀ y ∈ G k b.1, y ≤ a.1) : Dom (ThetaVTerm.theta k (a + omegaPow b).1) :=
  (dom_theta_iff _ _).mpr ⟨(a + omegaPow b).2.2, fun y hy =>
    lt_of_le_of_lt' ((mem_G_add_omegaPow hy).elim (ha y) (hb y)) (lt_add_omegaPow_hull a b)⟩

/-- **The domain lemma of the collapsing theorem** (the audit's statement, verbatim, for the
level-free operator): `HullHypS k α X`, `α, β ∈ H_α(X)` give `Dom (ϑ_k (α + ω^β))`. -/
theorem dom_add_omegaPow {k : ℕ} {a b : ThetaVNoteD} {X : Set ThetaVNoteD}
    (hX : HullHypS k a X) (ha : a ∈ HopS a X) (hb : b ∈ HopS a X) :
    Dom (ThetaVTerm.theta k (a + omegaPow b).1) :=
  dom_add_omegaPow_of_G_le (G_le_of_mem_HopS hX ha) (G_le_of_mem_HopS hX hb)

/-- `α, β ∈ H_α(X)` give `α + ω^β ∈ H_{α + ω^β}(X)`. -/
theorem add_omegaPow_mem_HopS {a b : ThetaVNoteD} {X : Set ThetaVNoteD}
    (ha : a ∈ HopS a X) (hb : b ∈ HopS a X) : a + omegaPow b ∈ HopS (a + omegaPow b) X :=
  HopS_subset_HopS (lt_add_omegaPow_hull a b) X
    ((HopS_nice a).add_mem ha ((HopS_nice a).omegaPow_mem hb))

/-- **Theorem 6.7's membership fact, with no `≺ Ω_{k+1}` bound**: `HullHypS k α X` and
`α, β ∈ H_α(X)` give `ϑ_k (α + ω^β) ∈ H_{α + ω^β}(X)`. -/
theorem theta_add_omegaPow_mem_HopS {k : ℕ} {a b : ThetaVNoteD} {X : Set ThetaVNoteD}
    (hX : HullHypS k a X) (ha : a ∈ HopS a X) (hb : b ∈ HopS a X) :
    thetaD k (a + omegaPow b) (dom_add_omegaPow hX ha hb) ∈ HopS (a + omegaPow b) X :=
  theta_mem_HopS k (add_omegaPow_mem_HopS ha hb) le_rfl (dom_add_omegaPow hX ha hb)

/-! ### The hull hypothesis at all levels `≥ k` (Buchholz's `𝒜(Θ; γ, κ, μ)` quantifies over
every `τ ⪰ κ`); it passes upward by definition and keeps every property used above -/

/-- `HullHypS j α X` for every level `j ≥ k`. -/
def HullHypGe (k : ℕ) (a : ThetaVNoteD) (X : Set ThetaVNoteD) : Prop :=
  ∀ j, k ≤ j → HullHypS j a X

theorem HullHypGe.hullHypS {k : ℕ} {a : ThetaVNoteD} {X : Set ThetaVNoteD}
    (h : HullHypGe k a X) : HullHypS k a X := h k le_rfl

theorem HullHypGe.up {k j : ℕ} {a : ThetaVNoteD} {X : Set ThetaVNoteD} (h : HullHypGe k a X)
    (hkj : k ≤ j) : HullHypGe j a X :=
  fun i hji => h i (le_trans hkj hji)

theorem HullHypGe.mono {k : ℕ} {a b : ThetaVNoteD} {X : Set ThetaVNoteD} (h : HullHypGe k a X)
    (hab : a ≤ b) : HullHypGe k b X :=
  fun j hkj => (h j hkj).mono hab

theorem HullHypGe.lt_theta {k : ℕ} {a c d : ThetaVNoteD} {X : Set ThetaVNoteD}
    (h : HullHypGe k a X) (hac : a < c) (hc : Dom (ThetaVTerm.theta k c.1)) (hd : d ∈ HopS a X)
    (hΩ : d < Omega k) : d < thetaD k c hc :=
  h.hullHypS.lt_theta hac hc hd hΩ

theorem HullHypGe.union_singleton {k : ℕ} {a d g : ThetaVNoteD} {X : Set ThetaVNoteD}
    (h : HullHypGe k a X) (hd : d ∈ HopS a X) (hΩ : d < Omega k) (hgd : g < d) :
    HullHypGe k a (X ∪ {g}) := by
  intro j hkj
  have hkj' : Omega k ≤ Omega j := by
    rcases Nat.lt_or_eq_of_le hkj with h' | rfl
    · exact le_of_lt ((Omega_lt_Omega_iff k j).mpr h')
    · exact le_rfl
  exact (h j hkj).union_singleton hd (lt_of_lt_of_le hΩ hkj') hgd

theorem dom_add_omegaPow_ge {k : ℕ} {a b : ThetaVNoteD} {X : Set ThetaVNoteD}
    (hX : HullHypGe k a X) (ha : a ∈ HopS a X) (hb : b ∈ HopS a X) :
    Dom (ThetaVTerm.theta k (a + omegaPow b).1) :=
  dom_add_omegaPow hX.hullHypS ha hb

end ThetaVNoteD

end OrdinalAnalysis
