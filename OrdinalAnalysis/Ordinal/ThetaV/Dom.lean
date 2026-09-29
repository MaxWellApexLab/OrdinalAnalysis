/-
  The domain condition for the ϑ-notation with `Ω_ω`, and the sanity table of the design
  (`idomega_design.md` §2.2).

  Sources: G. Wilken, arXiv:2410.15953, §2.2 (Lemma 2.13: `α ∈ dom(ϑ̄_m) ⇔ K*_{m+1}(α) < α`),
  as in `ThetaW/Dom`.

  `G_k(α)` collects the arguments of the collapses of level `> k` in `α`, looking through those
  collapses and stopping at collapses of level `≤ k`:
    `G_k(Ω_{j+1}) = G_k(Ω_ω) = ∅`,  `G_k(ϑ_j ξ) = {ξ} ∪ G_k(ξ)` if `k < j`, `∅` if `j ≤ k`,
    `G_k(⟨α₀, …⟩) = ⋃ G_k(α_i)`.
  `Ω_ω` is not a collapse: it is a constant with no argument, so it contributes nothing to `G_k`
  (exactly as `Ω_{j+1}`).  A term is in the domain, `Dom`, if every subterm `ϑ_k ξ` has
  `G_k(ξ) ≺* ξ`.

  The descending sequences.  Without `Dom` the order is not well founded on normal terms, now
  also with `Ω_ω` at the bottom of the tower:
    `ϑ₀(Ω_ω) ≻ ϑ₀(ϑ₁(Ω_ω)) ≻ ϑ₀(ϑ₁(ϑ₂(Ω_ω))) ≻ ⋯`   (`towerW`, `ThetaVNote.not_wellFoundedLT`).
  `Dom` excludes it from the second term on, exactly as it excludes the old sequence
  `ϑ₀(Ω₂) ≻ ϑ₀(ϑ₁(Ω₃)) ≻ ⋯`: `G₀(ϑ₁(Ω_ω)) = {Ω_ω} ⊀ ϑ₁(Ω_ω)` (`not_dom_towerW`).

  The sanity table (§2.2) is checked by `decide` at the end of the file (the `<` instance is
  computed with fuel, `ThetaV/Basic`); in particular `ϑ₀(ϑ_{1000} 0) ≺ ϑ₀(Ω_ω)`: the
  predecessors of the countable domain term `ϑ₀(Ω_ω)` have unbounded levels.  In general every
  normal `Ω_ω`-free countable term lies below `ϑ₀(Ω_ω)` (`lt_theta0_OmegaW_of_wFree`).
-/
import OrdinalAnalysis.Ordinal.ThetaV.Exponents

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaVTerm

/-! ### The argument sets `G_k` -/

mutual
/-- `G_k(α)`: the arguments of the collapses of level `> k` in `α`, looking through those
collapses (Wilken, arXiv:2410.15953, Definition 2.11: `K*_{k+1}`).  `Ω_{j+1}` and `Ω_ω`
contribute nothing. -/
def G (k : ℕ) : ThetaVTerm → List ThetaVTerm
  | Omega _ => []
  | OmegaW => []
  | theta j a => if k < j then a :: G k a else []
  | sum xs => GList k xs
/-- The union of the `G_k(α_i)` over a list. -/
def GList (k : ℕ) : List ThetaVTerm → List ThetaVTerm
  | [] => []
  | x :: xs => G k x ++ GList k xs
end

@[simp] theorem G_Omega (k j : ℕ) : G k (Omega j) = [] := by simp [G]

@[simp] theorem G_OmegaW (k : ℕ) : G k OmegaW = [] := by simp [G]

theorem G_theta_of_lt {k j : ℕ} (h : k < j) (a : ThetaVTerm) :
    G k (theta j a) = a :: G k a := by simp [G, h]

theorem G_theta_of_le {k j : ℕ} (h : j ≤ k) (a : ThetaVTerm) : G k (theta j a) = [] := by
  simp [G, Nat.not_lt.mpr h]

@[simp] theorem G_nil (k : ℕ) : G k (sum []) = [] := by simp [G, GList]

@[simp] theorem G_cons (k : ℕ) (x : ThetaVTerm) (xs : List ThetaVTerm) :
    G k (sum (x :: xs)) = G k x ++ G k (sum xs) := by simp [G, GList]

theorem mem_G_sum {k : ℕ} {g : ThetaVTerm} {xs : List ThetaVTerm} :
    g ∈ G k (sum xs) ↔ ∃ x ∈ xs, g ∈ G k x := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp [ih]

/-- The members of `G_k(α)` are proper subterms of `α`. -/
theorem l_lt_of_mem_G {k : ℕ} : ∀ {a x : ThetaVTerm}, x ∈ G k a → l x < l a
  | Omega _, x, h => by simp at h
  | OmegaW, x, h => by simp at h
  | theta j a, x, h => by
    by_cases hj : k < j
    · rw [G_theta_of_lt hj] at h
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · have := l_lt_of_mem_G h; simp; omega
    · rw [G_theta_of_le (Nat.le_of_not_lt hj)] at h; simp at h
  | sum xs, x, h => by
    obtain ⟨y, hy, hx⟩ := mem_G_sum.mp h
    have := l_lt_of_mem hy
    have := l_lt_of_mem_G hx
    omega
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hy

/-- The members of `G_k(α)` of a normal term are normal. -/
theorem NF.of_mem_G {k : ℕ} : ∀ {a x : ThetaVTerm}, NF a → x ∈ G k a → NF x
  | Omega _, x, _, h => by simp at h
  | OmegaW, x, _, h => by simp at h
  | theta j a, x, ha, h => by
    by_cases hj : k < j
    · rw [G_theta_of_lt hj] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ha.theta_arg
      · exact NF.of_mem_G ha.theta_arg h
    · rw [G_theta_of_le (Nat.le_of_not_lt hj)] at h; simp at h
  | sum xs, x, ha, h => by
    obtain ⟨y, hy, hx⟩ := mem_G_sum.mp h
    exact NF.of_mem_G (ha.of_mem hy) hx
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hy

/-! ### The domain condition -/

mutual
/-- The domain condition, hereditarily: every subterm `ϑ_k ξ` has `G_k(ξ) ≺* ξ`. -/
def Dom : ThetaVTerm → Prop
  | Omega _ => True
  | OmegaW => True
  | theta k a => Dom a ∧ ∀ x ∈ G k a, x < a
  | sum xs => DomList xs
/-- Every entry of the list satisfies `Dom`. -/
def DomList : List ThetaVTerm → Prop
  | [] => True
  | x :: xs => Dom x ∧ DomList xs
end

mutual
/-- A decision procedure for `Dom`. -/
def decDom : (a : ThetaVTerm) → Decidable (Dom a)
  | Omega _ => isTrue (by simp [Dom])
  | OmegaW => isTrue (by simp [Dom])
  | theta k a =>
    match decDom a with
    | isTrue h =>
      if hG : ∀ x ∈ G k a, x < a then isTrue (by simp only [Dom]; exact ⟨h, hG⟩)
      else isFalse (by simp only [Dom]; exact fun h' => hG h'.2)
    | isFalse h => isFalse (by simp only [Dom]; exact fun h' => h h'.1)
  | sum xs =>
    match decDomList xs with
    | isTrue h => isTrue (by simp only [Dom]; exact h)
    | isFalse h => isFalse (by simp only [Dom]; exact h)
/-- A decision procedure for `DomList`. -/
def decDomList : (xs : List ThetaVTerm) → Decidable (DomList xs)
  | [] => isTrue (by simp [DomList])
  | x :: xs =>
    match decDom x, decDomList xs with
    | isTrue h1, isTrue h2 => isTrue (by simp only [DomList]; exact ⟨h1, h2⟩)
    | isFalse h1, _ => isFalse (by simp only [DomList]; exact fun h => h1 h.1)
    | _, isFalse h2 => isFalse (by simp only [DomList]; exact fun h => h2 h.2)
end

instance : DecidablePred Dom := decDom

@[simp] theorem dom_Omega (k : ℕ) : Dom (Omega k) := by simp [Dom]

@[simp] theorem dom_OmegaW : Dom OmegaW := by simp [Dom]

theorem dom_theta_iff (k : ℕ) (a : ThetaVTerm) :
    Dom (theta k a) ↔ Dom a ∧ ∀ x ∈ G k a, x < a := by simp [Dom]

theorem domList_iff {xs : List ThetaVTerm} : DomList xs ↔ ∀ x ∈ xs, Dom x := by
  induction xs with
  | nil => simp [DomList]
  | cons y ys ih => simp [DomList, ih]

theorem dom_sum_iff (xs : List ThetaVTerm) : Dom (sum xs) ↔ ∀ x ∈ xs, Dom x := by
  simp only [Dom, domList_iff]

theorem dom_zero : Dom zero := by simp [zero, dom_sum_iff]

theorem Dom.of_mem {x : ThetaVTerm} {xs : List ThetaVTerm} (h : Dom (sum xs)) (hx : x ∈ xs) :
    Dom x :=
  (dom_sum_iff xs).mp h x hx

theorem Dom.theta_arg {k : ℕ} {a : ThetaVTerm} (h : Dom (theta k a)) : Dom a :=
  ((dom_theta_iff k a).mp h).1

theorem Dom.G_lt {k : ℕ} {a x : ThetaVTerm} (h : Dom (theta k a)) (hx : x ∈ G k a) : x < a :=
  ((dom_theta_iff k a).mp h).2 x hx

/-- `Dom` of a Cantor sum is `Dom` of its exponents. -/
theorem dom_ofList_iff {xs : List ThetaVTerm} : Dom (ofList xs) ↔ ∀ x ∈ xs, Dom x := by
  match xs with
  | [] => simp [dom_sum_iff]
  | [x] =>
    by_cases h : IsPrin x
    · rw [ofList_singleton_prin h]; simp
    · rw [ofList_singleton_not_prin h]; exact dom_sum_iff [x]
  | _ :: _ :: _ => exact dom_sum_iff _

/-- The level-`k` coefficients of a domain term are domain terms. -/
theorem Dom.of_mem_E {k : ℕ} : ∀ {a g : ThetaVTerm}, Dom a → g ∈ E k a → Dom g
  | Omega _, g, _, h => by simp at h
  | OmegaW, g, _, h => by simp at h
  | theta j a, g, ha, h => by
    by_cases hj : j ≤ k
    · rw [E_theta_of_le hj] at h; simp at h; exact h ▸ ha
    · rw [E_theta_of_lt (Nat.lt_of_not_le hj)] at h
      exact Dom.of_mem_E ha.theta_arg h
  | sum xs, g, ha, h => by
    obtain ⟨x, hx, hg⟩ := mem_E_sum.mp h
    exact Dom.of_mem_E (ha.of_mem hx) hg
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hx

/-- The members of `G_k(α)` of a domain term are domain terms. -/
theorem Dom.of_mem_G {k : ℕ} : ∀ {a x : ThetaVTerm}, Dom a → x ∈ G k a → Dom x
  | Omega _, x, _, h => by simp at h
  | OmegaW, x, _, h => by simp at h
  | theta j a, x, ha, h => by
    by_cases hj : k < j
    · rw [G_theta_of_lt hj] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ha.theta_arg
      · exact Dom.of_mem_G ha.theta_arg h
    · rw [G_theta_of_le (Nat.le_of_not_lt hj)] at h; simp at h
  | sum xs, x, ha, h => by
    obtain ⟨y, hy, hx⟩ := mem_G_sum.mp h
    exact Dom.of_mem_G (ha.of_mem hy) hx
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hy

/-- `ϑ_k` may be applied to a domain term without collapses of level `> k` at top level. -/
theorem dom_theta_of_G_nil {k : ℕ} {a : ThetaVTerm} (ha : Dom a) (hG : G k a = []) :
    Dom (theta k a) :=
  (dom_theta_iff k a).mpr ⟨ha, by simp [hG]⟩

/-- `ϑ_k(Ω_ω)` is in the domain for every `k`: `G_k(Ω_ω) = ∅`. -/
theorem dom_theta_OmegaW (k : ℕ) : Dom (theta k OmegaW) :=
  dom_theta_of_G_nil dom_OmegaW (G_OmegaW k)

/-! ### The towers ending in `Ω_ω` -/

/-- `towerW j m = ϑ_j(ϑ_{j+1}(⋯ ϑ_{j+m-1}(Ω_ω) ⋯))`, with `m` collapses. -/
def towerW (j : ℕ) : ℕ → ThetaVTerm
  | 0 => OmegaW
  | m + 1 => theta j (towerW (j + 1) m)

@[simp] theorem towerW_zero (j : ℕ) : towerW j 0 = OmegaW := rfl

@[simp] theorem towerW_succ (j m : ℕ) : towerW j (m + 1) = theta j (towerW (j + 1) m) := rfl

theorem nf_towerW : ∀ (m j : ℕ), NF (towerW j m)
  | 0, _ => nf_OmegaW
  | m + 1, j => (nf_theta_iff j _).mpr (nf_towerW m (j + 1))

theorem isPrin_towerW : ∀ (j m : ℕ), IsPrin (towerW j m)
  | _, 0 => trivial
  | _, _ + 1 => trivial

/-- A tower all of whose collapses have level `> k` has no level-`k` coefficients. -/
theorem E_towerW_of_lt : ∀ (m : ℕ) {k j : ℕ}, k < j → E k (towerW j m) = []
  | 0, _, _, _ => E_OmegaW _
  | m + 1, k, j, h => by
    rw [towerW_succ, E_theta_of_lt h]
    exact E_towerW_of_lt m (by omega)

/-- Each tower is below the previous one: `towerW j (m+1) ≺ towerW j m`. -/
theorem towerW_succ_lt : ∀ (m j : ℕ), towerW j (m + 1) < towerW j m
  | 0, j => theta_lt_OmegaW j _
  | m + 1, j => by
    rw [towerW_succ j (m + 1), towerW_succ j m]
    refine theta_lt_theta_of_lt (towerW_succ_lt m (j + 1)) ?_
    rw [E_towerW_of_lt (m + 1) (Nat.lt_succ_self j)]
    simp

/-- `ϑ_j(Ω_ω)` is in the domain. -/
theorem dom_towerW_one (j : ℕ) : Dom (towerW j 1) := dom_theta_OmegaW j

/-- `ϑ_j(ϑ_{j+1}(⋯))` is not in the domain: the argument of `ϑ_{j+1}` (`Ω_ω` or a
`ϑ_{j+2}`-term) lies above `ϑ_{j+1}(⋯)` itself. -/
theorem not_dom_towerW (j m : ℕ) : ¬ Dom (towerW j (m + 2)) := by
  intro h
  rw [towerW_succ, towerW_succ] at h
  have hlt := h.G_lt (x := towerW (j + 2) m) (by rw [G_theta_of_lt (Nat.lt_succ_self j)]; simp)
  cases m with
  | zero => exact not_OmegaW_lt_theta _ _ hlt
  | succ m =>
    rw [towerW_succ] at hlt
    exact not_theta_lt_theta_of_lt_level _ _ (by omega) hlt

/-! ### `Ω_ω`-free countable terms lie below `ϑ₀(Ω_ω)` -/

/-- Every normal `Ω_ω`-free term below `Ω₁` lies below `ϑ₀(Ω_ω)`: the countable part of the
old notation is an initial segment of the countable part, bounded by `ϑ₀(Ω_ω)`. -/
theorem lt_theta0_OmegaW_of_wFree : ∀ {t : ThetaVTerm}, NF t → WFree t → t < Omega 0 →
    t < theta 0 OmegaW
  | Omega j, _, _, h => absurd ((Omega_lt_Omega_iff j 0).mp h) (Nat.not_lt_zero j)
  | OmegaW, _, h, _ => absurd h not_wFree_OmegaW
  | theta j a, ht, hW, h => by
    have hj : j = 0 := Nat.le_zero.mp ((theta_lt_Omega_iff j 0 a).mp h)
    subst hj
    have hWa : WFree a := (wFree_theta_iff 0 a).mp hW
    refine theta_lt_theta_of_lt (lt_OmegaW_of_wFree hWa) fun g hg => ?_
    exact lt_theta0_OmegaW_of_wFree (NF.of_mem_E ht.theta_arg hg) (WFree.of_mem_E hWa hg)
      (lt_Omega_of_mem_E hg)
  | sum xs, ht, hW, h => by
    have hxs := (sum_lt_prin_iff (isPrin_Omega 0) ht.desc).mp h
    refine (sum_lt_prin_iff (isPrin_theta 0 _) ht.desc).mpr fun x hx => ?_
    exact lt_theta0_OmegaW_of_wFree (ht.of_mem hx) ((wFree_sum_iff xs).mp hW x hx) (hxs x hx)
termination_by t => l t
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · exact l_lt_of_mem hx

end ThetaVTerm

namespace ThetaVNote

/-- The descending sequence `ϑ₀(Ω_ω) ≻ ϑ₀(ϑ₁(Ω_ω)) ≻ ⋯` as normal notations. -/
def descSeqW (m : ℕ) : ThetaVNote :=
  ⟨ThetaVTerm.towerW 0 (m + 1), ThetaVTerm.nf_towerW (m + 1) 0⟩

theorem descSeqW_succ_lt (m : ℕ) : descSeqW (m + 1) < descSeqW m :=
  ThetaVTerm.towerW_succ_lt (m + 1) 0

private theorem not_acc_of_desc {β : Type} {r : β → β → Prop} (f : ℕ → β)
    (hf : ∀ n, r (f (n + 1)) (f n)) {a : β} (ha : Acc r a) : ∀ n, f n ≠ a := by
  induction ha with
  | intro a _ ih =>
  intro n hn
  exact ih (f (n + 1)) (hn ▸ hf n) (n + 1) rfl

/-- Without the domain condition the order on normal terms is not well founded. -/
theorem not_wellFoundedLT : ¬ WellFoundedLT ThetaVNote := by
  intro h
  exact not_acc_of_desc descSeqW descSeqW_succ_lt (h.wf.apply (descSeqW 0)) 0 rfl

/-- The terms of the sequence leave the domain from the second term on. -/
theorem not_dom_descSeqW (m : ℕ) : ¬ ThetaVTerm.Dom (descSeqW (m + 1)).1 :=
  ThetaVTerm.not_dom_towerW 0 m

end ThetaVNote

/-- The ϑ-notation with `Ω_ω` and the domain condition: normal terms all of whose collapses
`ϑ_k ξ` satisfy `G_k(ξ) ≺* ξ`, all levels. -/
def ThetaVNoteD : Type := {t : ThetaVTerm // ThetaVTerm.NF t ∧ ThetaVTerm.Dom t}

instance : DecidableEq ThetaVNoteD :=
  inferInstanceAs (DecidableEq {t : ThetaVTerm // ThetaVTerm.NF t ∧ ThetaVTerm.Dom t})

/-- The order of `ThetaV/Order`, restricted to the domain terms. -/
instance ThetaVNoteD.linearOrder : LinearOrder ThetaVNoteD :=
  inferInstanceAs (LinearOrder {t : ThetaVTerm // ThetaVTerm.NF t ∧ ThetaVTerm.Dom t})

namespace ThetaVNoteD

theorem lt_iff {a b : ThetaVNoteD} : a < b ↔ a.1 < b.1 := Iff.rfl

theorem le_iff {a b : ThetaVNoteD} : a ≤ b ↔ a.1 ≤ b.1 := Iff.rfl

/-- The notation `0`. -/
def zero : ThetaVNoteD := ⟨ThetaVTerm.zero, ThetaVTerm.nf_zero, ThetaVTerm.dom_zero⟩

/-- The notation `Ω_{k+1}`. -/
def Omega (k : ℕ) : ThetaVNoteD :=
  ⟨ThetaVTerm.Omega k, ThetaVTerm.nf_Omega k, ThetaVTerm.dom_Omega k⟩

/-- The notation `Ω_ω`. -/
def OmegaW : ThetaVNoteD := ⟨ThetaVTerm.OmegaW, ThetaVTerm.nf_OmegaW, ThetaVTerm.dom_OmegaW⟩

/-- The notation `ϑ_k(Ω_ω)`. -/
def thetaOmegaW (k : ℕ) : ThetaVNoteD :=
  ⟨ThetaVTerm.theta k ThetaVTerm.OmegaW, by simp, ThetaVTerm.dom_theta_OmegaW k⟩

/-- `0` is the least notation. -/
instance : OrderBot ThetaVNoteD where
  bot := zero
  bot_le a := ThetaVTerm.zero_le' a.1

theorem Omega_lt_OmegaW (k : ℕ) : Omega k < OmegaW := ThetaVTerm.Omega_lt_OmegaW k

theorem thetaOmegaW_lt_Omega (k : ℕ) : thetaOmegaW k < Omega k :=
  ThetaVTerm.theta_lt_Omega_self k _

end ThetaVNoteD

/-! ### The sanity table (`idomega_design.md` §2.2), by `decide` -/

namespace ThetaVTerm

/-- `Ω_ω + 1 = ω^{Ω_ω} + ω^0`. -/
def OmegaWSucc : ThetaVTerm := sum [OmegaW, zero]

/-- `ω^{Ω_ω + 1}`. -/
def omegaPowOmegaWSucc : ThetaVTerm := sum [OmegaWSucc]

-- normal forms
example : NF OmegaWSucc := by decide
example : NF omegaPowOmegaWSucc := by decide
example : NF (theta 0 omegaPowOmegaWSucc) := by decide

-- `ϑ₀(ϑ_k 0) ≺ ϑ₀(Ω_ω)` for `k ≤ 5`
example : theta 0 (theta 0 zero) < theta 0 OmegaW := by decide
example : theta 0 (theta 1 zero) < theta 0 OmegaW := by decide
example : theta 0 (theta 2 zero) < theta 0 OmegaW := by decide
example : theta 0 (theta 3 zero) < theta 0 OmegaW := by decide
example : theta 0 (theta 4 zero) < theta 0 OmegaW := by decide
example : theta 0 (theta 5 zero) < theta 0 OmegaW := by decide

-- `ϑ₀(Ω_ω) ≺ ϑ₀(Ω_ω + 1) ≺ ϑ₀(ω^{Ω_ω+1})`, all in the domain
example : theta 0 OmegaW < theta 0 OmegaWSucc := by decide
example : theta 0 OmegaWSucc < theta 0 omegaPowOmegaWSucc := by decide
example : Dom (theta 0 OmegaWSucc) := by decide
example : Dom (theta 0 omegaPowOmegaWSucc) := by decide
example : theta 0 omegaPowOmegaWSucc < Omega 0 := by decide

-- `ϑ₄(Ω_ω) ≺ Ω₅` and `Dom (ϑ₄ Ω_ω)`
example : theta 4 OmegaW < Omega 4 := by decide
example : Omega 3 < theta 4 OmegaW := by decide
example : Dom (theta 4 OmegaW) := by decide

-- `¬ Dom (ϑ₀(ϑ₄ Ω_ω))`: `G₀(ϑ₄ Ω_ω) = {Ω_ω} ⊀ ϑ₄ Ω_ω`
example : G 0 (theta 4 OmegaW) = [OmegaW] := by decide
example : ¬ OmegaW < theta 4 OmegaW := by decide
example : ¬ Dom (theta 0 (theta 4 OmegaW)) := by decide

-- unbounded predecessor levels: `ϑ₀(ϑ₁₀₀₀ 0) ≺ ϑ₀(Ω_ω)`, both in the domain
example : theta 0 (theta 1000 zero) < theta 0 OmegaW := by decide
example : Dom (theta 0 (theta 1000 zero)) := by decide
example : Dom (theta 0 OmegaW) := by decide
example : NF (theta 0 (theta 1000 zero)) := by decide

-- the descending chain with `Ω_ω` at the bottom: descending, and outside `Dom` from the
-- second term on
example : theta 0 (theta 1 OmegaW) < theta 0 OmegaW := by decide
example : theta 0 (theta 1 (theta 2 OmegaW)) < theta 0 (theta 1 OmegaW) := by decide
example : theta 0 (theta 1 (theta 2 (theta 3 OmegaW))) < theta 0 (theta 1 (theta 2 OmegaW)) := by
  decide
example : ¬ Dom (theta 0 (theta 1 OmegaW)) := by decide
example : ¬ Dom (theta 0 (theta 1 (theta 2 OmegaW))) := by decide
example : ¬ Dom (theta 0 (theta 1 (theta 2 (theta 3 OmegaW)))) := by decide

-- the old chain `ϑ₀(Ω₂) ≻ ϑ₀(ϑ₁(Ω₃)) ≻ ⋯` is excluded in the same way
example : theta 0 (theta 1 (Omega 2)) < theta 0 (Omega 1) := by decide
example : Dom (theta 0 (Omega 1)) := by decide
example : ¬ Dom (theta 0 (theta 1 (Omega 2))) := by decide

-- the old countable part sits below `ϑ₀(Ω_ω)`
example : theta 0 (Omega 7) < theta 0 OmegaW := by decide
example : theta 0 (theta 3 (Omega 9)) < theta 0 OmegaW := by decide
example : sum [theta 0 (Omega 7), theta 0 (Omega 7)] < theta 0 OmegaW := by decide

end ThetaVTerm

end OrdinalAnalysis
