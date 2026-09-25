/-
  The domain condition of the simultaneously defined ϑ-functions.

  Sources.
  * G. Wilken, *Fundamental sequences based on localization*, arXiv:2410.15953, §2.2, which
    restates A. Weiermann and G. Wilken, *Ordinal arithmetic with simultaneously defined
    theta-functions*, Math. Log. Quart. 57 (2011) 116–132: Definition 2.7 (the hulls
    `C̄_i(α, β)`, closed under `ϑ̄_j` for all `j ≥ i` on arguments in `dom(ϑ̄_j) ∩ α`),
    Definition 2.11 (the sets `K*_i`), **Lemma 2.13**
      `α ∈ dom(ϑ̄_m)  ⇔  K*_{m+1}(α) < α`,
    and Proposition 2.15 (for arguments in the domain, the comparison of two `ϑ̄_i`-terms is
    the clause used in `ThetaW/Basic`).
  * W. Buchholz, *A new system of proof-theoretic ordinal functions*, Ann. Pure Appl. Logic 32
    (1986): the same shape of normal form, `D_v b` normal iff `G_v(b) < b`.

  The raw system of `ThetaW/Basic` applies `ϑ_k` to every term.  The order is linear, but it
  is not well founded on the normal terms of all levels (`ThetaW/Descent`): the arguments
  `ϑ_{j+1}(Ω_{j+3})` of the descending sequence are not in the domain of `ϑ_j`, since the
  hull `C̄_j(α, ·)` generates `ϑ_{j+1}(ξ)` only from arguments `ξ < α`.

  `G_k(α)` is Wilken's `K*_{k+1}(α)`: the arguments of the collapses of level `> k` in `α`,
  looking through those collapses and stopping at collapses of level `≤ k`:
    `G_k(Ω_{j+1}) = ∅`,  `G_k(ϑ_j ξ) = {ξ} ∪ G_k(ξ)` if `k < j`, `∅` if `j ≤ k`,
    `G_k(⟨α₀, …⟩) = ⋃ G_k(α_i)`.
  (`Ω_{j+1}` is Wilken's `ϑ̄_{j+1}(0)`, whose argument `0` lies below every non-zero term, so it
  is left out.)  A term is in the domain, `Dom`, if every subterm `ϑ_k ξ` has `G_k(ξ) ≺* ξ`.

  The file proves: `Dom` is decidable, hereditary, closed under the Cantor-sum operations
  `toList`/`ofList` and under `E_k` and `G_k`; the descending sequence of `ThetaW/Descent` leaves
  the domain from its second term on; `c_n = ϑ₀(ϑ_n 0)` (intended value `ψ₀(ε_{Ω_n+1})`) and
  `ϑ₀(Ω_{n+1})` are in the domain for every `n`; every normal countable term all of whose
  levels are `< N` lies below `ϑ₀(Ω_{N+1})`; and the predecessors of a domain term need not
  have bounded levels: `ϑ₁(Ω₆) ≺ Ω₂`.
-/
import OrdinalAnalysis.Ordinal.ThetaW.Exponents
import OrdinalAnalysis.Ordinal.ThetaW.Descent

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

/-! ### The argument sets `G_k` -/

mutual
/-- `G_k(α)`: the arguments of the collapses of level `> k` in `α`, looking through those
collapses (Wilken, arXiv:2410.15953, Definition 2.11: `K*_{k+1}`). -/
def G (k : ℕ) : ThetaWTerm → List ThetaWTerm
  | Omega _ => []
  | theta j a => if k < j then a :: G k a else []
  | sum xs => GList k xs
/-- The union of the `G_k(α_i)` over a list. -/
def GList (k : ℕ) : List ThetaWTerm → List ThetaWTerm
  | [] => []
  | x :: xs => G k x ++ GList k xs
end

@[simp] theorem G_Omega (k j : ℕ) : G k (Omega j) = [] := by simp [G]

theorem G_theta_of_lt {k j : ℕ} (h : k < j) (a : ThetaWTerm) :
    G k (theta j a) = a :: G k a := by simp [G, h]

theorem G_theta_of_le {k j : ℕ} (h : j ≤ k) (a : ThetaWTerm) : G k (theta j a) = [] := by
  simp [G, Nat.not_lt.mpr h]

@[simp] theorem G_nil (k : ℕ) : G k (sum []) = [] := by simp [G, GList]

@[simp] theorem G_cons (k : ℕ) (x : ThetaWTerm) (xs : List ThetaWTerm) :
    G k (sum (x :: xs)) = G k x ++ G k (sum xs) := by simp [G, GList]

theorem mem_G_sum {k : ℕ} {g : ThetaWTerm} {xs : List ThetaWTerm} :
    g ∈ G k (sum xs) ↔ ∃ x ∈ xs, g ∈ G k x := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp [ih]

theorem mem_G_ofList {k : ℕ} {g : ThetaWTerm} {xs : List ThetaWTerm} :
    g ∈ G k (ofList xs) ↔ ∃ x ∈ xs, g ∈ G k x := by
  match xs with
  | [] => simp
  | [x] =>
    by_cases h : IsPrin x
    · rw [ofList_singleton_prin h]; simp
    · rw [ofList_singleton_not_prin h]; exact mem_G_sum
  | _ :: _ :: _ => exact mem_G_sum

/-- The members of `G_k(α)` are proper subterms of `α`. -/
theorem l_lt_of_mem_G {k : ℕ} : ∀ {a x : ThetaWTerm}, x ∈ G k a → l x < l a
  | Omega _, x, h => by simp at h
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
theorem NF.of_mem_G {k : ℕ} : ∀ {a x : ThetaWTerm}, NF a → x ∈ G k a → NF x
  | Omega _, x, _, h => by simp at h
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
/-- The domain condition, hereditarily: every subterm `ϑ_k ξ` has `G_k(ξ) ≺* ξ` (Wilken,
arXiv:2410.15953, Lemma 2.13; Weiermann–Wilken 2011, Lemma 4.3). -/
def Dom : ThetaWTerm → Prop
  | Omega _ => True
  | theta k a => Dom a ∧ ∀ x ∈ G k a, x < a
  | sum xs => DomList xs
/-- Every entry of the list satisfies `Dom`. -/
def DomList : List ThetaWTerm → Prop
  | [] => True
  | x :: xs => Dom x ∧ DomList xs
end

mutual
/-- A decision procedure for `Dom`. -/
def decDom : (a : ThetaWTerm) → Decidable (Dom a)
  | Omega _ => isTrue (by simp [Dom])
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
def decDomList : (xs : List ThetaWTerm) → Decidable (DomList xs)
  | [] => isTrue (by simp [DomList])
  | x :: xs =>
    match decDom x, decDomList xs with
    | isTrue h1, isTrue h2 => isTrue (by simp only [DomList]; exact ⟨h1, h2⟩)
    | isFalse h1, _ => isFalse (by simp only [DomList]; exact fun h => h1 h.1)
    | _, isFalse h2 => isFalse (by simp only [DomList]; exact fun h => h2 h.2)
end

instance : DecidablePred Dom := decDom

@[simp] theorem dom_Omega (k : ℕ) : Dom (Omega k) := by simp [Dom]

theorem dom_theta_iff (k : ℕ) (a : ThetaWTerm) :
    Dom (theta k a) ↔ Dom a ∧ ∀ x ∈ G k a, x < a := by simp [Dom]

theorem domList_iff {xs : List ThetaWTerm} : DomList xs ↔ ∀ x ∈ xs, Dom x := by
  induction xs with
  | nil => simp [DomList]
  | cons y ys ih => simp [DomList, ih]

theorem dom_sum_iff (xs : List ThetaWTerm) : Dom (sum xs) ↔ ∀ x ∈ xs, Dom x := by
  simp only [Dom, domList_iff]

theorem dom_zero : Dom zero := by simp [zero, dom_sum_iff]

theorem Dom.of_mem {x : ThetaWTerm} {xs : List ThetaWTerm} (h : Dom (sum xs)) (hx : x ∈ xs) :
    Dom x :=
  (dom_sum_iff xs).mp h x hx

theorem Dom.theta_arg {k : ℕ} {a : ThetaWTerm} (h : Dom (theta k a)) : Dom a :=
  ((dom_theta_iff k a).mp h).1

theorem Dom.G_lt {k : ℕ} {a x : ThetaWTerm} (h : Dom (theta k a)) (hx : x ∈ G k a) : x < a :=
  ((dom_theta_iff k a).mp h).2 x hx

/-- `Dom` of a Cantor sum is `Dom` of its exponents. -/
theorem dom_ofList_iff {xs : List ThetaWTerm} : Dom (ofList xs) ↔ ∀ x ∈ xs, Dom x := by
  match xs with
  | [] => simp [dom_sum_iff]
  | [x] =>
    by_cases h : IsPrin x
    · rw [ofList_singleton_prin h]; simp
    · rw [ofList_singleton_not_prin h]; exact dom_sum_iff [x]
  | _ :: _ :: _ => exact dom_sum_iff _

/-- The Cantor exponents of a domain term are domain terms. -/
theorem Dom.of_mem_toList {t x : ThetaWTerm} (h : Dom t) (hx : x ∈ toList t) : Dom x := by
  cases t with
  | Omega _ => simp [toList] at hx; exact hx ▸ h
  | theta _ _ => simp [toList] at hx; exact hx ▸ h
  | sum xs => exact h.of_mem hx

/-- The level-`k` coefficients of a domain term are domain terms. -/
theorem Dom.of_mem_E {k : ℕ} : ∀ {a g : ThetaWTerm}, Dom a → g ∈ E k a → Dom g
  | Omega _, g, _, h => by simp at h
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
theorem Dom.of_mem_G {k : ℕ} : ∀ {a x : ThetaWTerm}, Dom a → x ∈ G k a → Dom x
  | Omega _, x, _, h => by simp at h
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
theorem dom_theta_of_G_nil {k : ℕ} {a : ThetaWTerm} (ha : Dom a) (hG : G k a = []) :
    Dom (theta k a) :=
  (dom_theta_iff k a).mpr ⟨ha, by simp [hG]⟩

/-- `ϑ_k(Ω_{n+1})` is in the domain for all `k` and `n`. -/
theorem dom_theta_Omega (k n : ℕ) : Dom (theta k (Omega n)) :=
  dom_theta_of_G_nil (dom_Omega n) (G_Omega k n)

/-! ### The descending sequence leaves the domain -/

theorem isPrin_tower : ∀ (j m : ℕ), IsPrin (tower j m)
  | _, 0 => trivial
  | _, _ + 1 => trivial

theorem dom_tower_zero (j : ℕ) : Dom (tower j 0) := dom_Omega j

/-- `ϑ_j(Ω_{j+2})` is in the domain. -/
theorem dom_tower_one (j : ℕ) : Dom (tower j 1) := dom_theta_Omega j (j + 1)

/-- `ϑ_j(ϑ_{j+1}(⋯))` is not in the domain: the argument of `ϑ_{j+1}` has a higher position
than `ϑ_{j+1}(⋯)` itself. -/
theorem not_dom_tower (j m : ℕ) : ¬ Dom (tower j (m + 2)) := by
  intro h
  rw [tower_succ, tower_succ] at h
  have hlt := h.G_lt (x := tower (j + 2) m) (by rw [G_theta_of_lt (Nat.lt_succ_self j)]; simp)
  have hk : key (theta (j + 1) (tower (j + 2) m)) < key (tower (j + 2) m) := by
    cases m with
    | zero => simp; omega
    | succ m => simp
  exact lt_asymm' hlt (prin_lt_of_key_lt trivial (isPrin_tower _ _) hk)

/-- The terms `descSeq m = tower 0 (m + 1)` of the descending sequence are outside the domain
for `m ≥ 1`. -/
theorem not_dom_descSeq (m : ℕ) : ¬ Dom (ThetaWNote.descSeq (m + 1)).1 :=
  not_dom_tower 0 m

/-! ### The terms `c_n` and a cofinal family below `Ω₁` -/

/-- `c_n = ϑ₀(ϑ_n 0)`; intended value `ψ₀(ε_{Ω_n+1})` (for `n ≥ 1`). -/
def cTerm (n : ℕ) : ThetaWTerm := theta 0 (theta n zero)

theorem nf_cTerm (n : ℕ) : NF (cTerm n) := by
  simp [cTerm, nf_zero]

theorem dom_cTerm (n : ℕ) : Dom (cTerm n) := by
  have h1 : Dom (theta n zero) := dom_theta_of_G_nil dom_zero (by simp [zero])
  refine (dom_theta_iff 0 _).mpr ⟨h1, fun x hx => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [G_theta_of_le le_rfl] at hx; simp at hx
  · rw [G_theta_of_lt hn] at hx
    simp [zero] at hx
    subst hx
    exact nil_lt_theta n _

theorem cTerm_lt_Omega0 (n : ℕ) : cTerm n < Omega 0 := theta_lt_Omega_self 0 _

/-- Level bounds are monotone. -/
theorem LevLT.mono {n m : ℕ} (hnm : n ≤ m) : ∀ {t : ThetaWTerm}, LevLT n t → LevLT m t
  | Omega k, h => by simp at h ⊢; omega
  | theta k a, h => by
    rw [levLT_theta] at h ⊢
    exact ⟨by omega, LevLT.mono hnm h.2⟩
  | sum xs, h => by
    rw [levLT_sum_iff] at h ⊢
    exact fun x hx => LevLT.mono hnm (h x hx)
termination_by t => l t
decreasing_by
  · simp
  · exact l_lt_of_mem hx

/-- Every term has a level bound. -/
theorem exists_levLT : ∀ t : ThetaWTerm, ∃ n, LevLT n t
  | Omega k => ⟨k + 1, by simp⟩
  | theta k a => by
    obtain ⟨n, hn⟩ := exists_levLT a
    exact ⟨max n (k + 1), (levLT_theta _ k a).mpr
      ⟨by omega, hn.mono (le_max_left _ _)⟩⟩
  | sum xs => by
    have : ∀ ys : List ThetaWTerm, (∀ y ∈ ys, ∃ n, LevLT n y) → ∃ n, ∀ y ∈ ys, LevLT n y := by
      intro ys
      induction ys with
      | nil => intro _; exact ⟨0, by simp⟩
      | cons y ys ih =>
        intro h
        obtain ⟨n, hn⟩ := h y List.mem_cons_self
        obtain ⟨m, hm⟩ := ih (fun z hz => h z (List.mem_cons_of_mem y hz))
        refine ⟨max n m, fun z hz => ?_⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hn.mono (le_max_left _ _)
        · exact (hm z hz).mono (le_max_right _ _)
    obtain ⟨n, hn⟩ := this xs (fun x hx => exists_levLT x)
    exact ⟨n, (levLT_sum_iff n xs).mpr hn⟩
termination_by t => l t
decreasing_by
  · simp
  · exact l_lt_of_mem hx

/-- A term all of whose levels are `< n` lies below `Ω_{n+1}` (`Omega n`). -/
theorem lt_Omega_of_levLT {n : ℕ} : ∀ {t : ThetaWTerm}, LevLT n t → t < Omega n
  | Omega k, h => (Omega_lt_Omega_iff k n).mpr ((levLT_Omega n k).mp h)
  | theta k a, h => (theta_lt_Omega_iff k n a).mpr (Nat.le_of_lt ((levLT_theta n k a).mp h).1)
  | sum [], _ => nil_lt_Omega n
  | sum (x :: xs), h =>
    (cons_lt_Omega_iff n x xs).mpr (lt_Omega_of_levLT ((levLT_sum_iff n _).mp h x
      List.mem_cons_self))
termination_by t => l t
decreasing_by simp; omega

/-- Cofinality below `Ω₁`: every normal countable term whose levels are `< N` lies below
`ϑ₀(Ω_{N+1})`, a term of the domain.  So the countable part of the notation is the union of
the segments below `ϑ₀(Ω_{N+1})`, intended value `sup_N ψ₀(Ω_{N+1}) = ψ₀(Ω_ω)`. -/
theorem lt_theta0_Omega_of_levLT {N : ℕ} : ∀ {t : ThetaWTerm}, NF t → LevLT N t →
    t < Omega 0 → t < theta 0 (Omega N)
  | Omega j, _, _, h => absurd ((Omega_lt_Omega_iff j 0).mp h) (Nat.not_lt_zero j)
  | theta j a, ht, hL, h => by
    have hj : j = 0 := Nat.le_zero.mp ((theta_lt_Omega_iff j 0 a).mp h)
    subst hj
    have hLa : LevLT N a := ((levLT_theta N 0 a).mp hL).2
    refine theta_lt_theta_of_lt (lt_Omega_of_levLT hLa) fun g hg => ?_
    exact lt_theta0_Omega_of_levLT (NF.of_mem_E ht.theta_arg hg) (LevLT.of_mem_E hLa hg)
      (lt_Omega_of_mem_E hg)
  | sum xs, ht, hL, h => by
    have hxs := (sum_lt_prin_iff (isPrin_Omega 0) ht.desc).mp h
    refine (sum_lt_prin_iff (isPrin_theta 0 _) ht.desc).mpr fun x hx => ?_
    exact lt_theta0_Omega_of_levLT (ht.of_mem hx) ((levLT_sum_iff N xs).mp hL x hx) (hxs x hx)
termination_by t => l t
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · exact l_lt_of_mem hx

/-! ### Predecessors of a domain term may have unbounded levels -/

/-- `ϑ₁(Ω₆) ≺ Ω₂`: a term of the domain with a level above those of `Ω₂` lies below `Ω₂`.
(Buchholz's `ψ₁(Ω₆) < Ω₂` likewise.)  So the predecessors of an uncountable domain term are
not confined to a level-bounded fragment. -/
theorem theta1_Omega5_lt_Omega1 : theta 1 (Omega 5) < Omega 1 :=
  (theta_lt_Omega_iff 1 1 _).mpr le_rfl

theorem dom_theta1_Omega5 : Dom (theta 1 (Omega 5)) := dom_theta_Omega 1 5

theorem not_levLT_theta1_Omega5 : ¬ LevLT 2 (theta 1 (Omega 5)) := by simp

theorem levLT_Omega1 : LevLT 2 (Omega 1) := by simp

end ThetaWTerm

/-- The multi-level ϑ-notation with the domain condition: normal terms all of whose
collapses `ϑ_k ξ` satisfy `G_k(ξ) ≺* ξ`, all levels. -/
def ThetaWNoteD : Type := {t : ThetaWTerm // ThetaWTerm.NF t ∧ ThetaWTerm.Dom t}

instance : DecidableEq ThetaWNoteD :=
  inferInstanceAs (DecidableEq {t : ThetaWTerm // ThetaWTerm.NF t ∧ ThetaWTerm.Dom t})

/-- The order of `ThetaW/Order`, restricted to the domain terms. -/
instance ThetaWNoteD.linearOrder : LinearOrder ThetaWNoteD :=
  inferInstanceAs (LinearOrder {t : ThetaWTerm // ThetaWTerm.NF t ∧ ThetaWTerm.Dom t})

namespace ThetaWNoteD

theorem lt_iff {a b : ThetaWNoteD} : a < b ↔ a.1 < b.1 := Iff.rfl

theorem le_iff {a b : ThetaWNoteD} : a ≤ b ↔ a.1 ≤ b.1 := Iff.rfl

/-- The notation `0`. -/
def zero : ThetaWNoteD := ⟨ThetaWTerm.zero, ThetaWTerm.nf_zero, ThetaWTerm.dom_zero⟩

/-- The notation `Ω_{k+1}`. -/
def Omega (k : ℕ) : ThetaWNoteD :=
  ⟨ThetaWTerm.Omega k, ThetaWTerm.nf_Omega k, ThetaWTerm.dom_Omega k⟩

/-- The notation `c_n = ϑ₀(ϑ_n 0)`, intended value `ψ₀(ε_{Ω_n+1})`. -/
def c (n : ℕ) : ThetaWNoteD := ⟨ThetaWTerm.cTerm n, ThetaWTerm.nf_cTerm n, ThetaWTerm.dom_cTerm n⟩

/-- The notation `ϑ₀(Ω_{n+1})`; these are cofinal below `Ω₁`. -/
def theta0Omega (n : ℕ) : ThetaWNoteD :=
  ⟨ThetaWTerm.theta 0 (ThetaWTerm.Omega n), by simp, ThetaWTerm.dom_theta_Omega 0 n⟩

/-- `0` is the least notation. -/
instance : OrderBot ThetaWNoteD where
  bot := zero
  bot_le a := ThetaWTerm.zero_le' a.1

/-- The countable domain terms are cofinally bounded by the `ϑ₀(Ω_{n+1})`. -/
theorem exists_lt_theta0Omega (a : ThetaWNoteD) (h : a.1 < ThetaWTerm.Omega 0) :
    ∃ n, a < theta0Omega n := by
  obtain ⟨n, hn⟩ := ThetaWTerm.exists_levLT a.1
  exact ⟨n, ThetaWTerm.lt_theta0_Omega_of_levLT a.2.1 hn h⟩

end ThetaWNoteD

end OrdinalAnalysis
