/-
  Well-foundedness of the ϑ-order with `Ω_ω` on the normal domain terms, all levels.

  Sources: W. Buchholz and W. Pohlers, *Provable wellorderings of formal theories for
  transfinitely iterated inductive definitions*, J. Symbolic Logic 43 (1978), pp. 121–123
  (Lemmas 1–3, Theorem 1, (10)–(12): the distinguished classes of all levels at once, the class
  `M`, and the main lemma (11) for all levels simultaneously); T. Arai, arXiv:2304.00246, §1.6
  (the distinguished-class argument for one collapse).  The domain condition is Wilken's
  (arXiv:2410.15953, Lemma 2.13), see `ThetaV/Dom`.

  The skeleton argument of `ThetaW/WellFoundedD` does not apply: it bounds the levels of the
  predecessors of a countable term, and `ϑ₀(ϑ_k 0) ≺ ϑ₀(Ω_ω)` for every `k` (`ThetaV/Dom`).  The
  classes are built bottom-up instead, by recursion on the level, and no level bound is used.

  * `Low k t`: for every `j < k`, the level-`j` coefficients of `t` are in `W j`;
    `Mk k t := Dom t ∧ Low k t`;  `W k t`: `t` is normal, `t ≺ Ω_{k+1}`, `t ∈ Mk k`, and `t` is
    accessible for `≺` restricted to `Mk k`.  (`W k` is BP78's `W_k`, `Mk k` their `M_k`.)
  * `Mall t`: for every `j`, the level-`j` coefficients of `t` are in `W j`;
    `MM t := Dom t ∧ Mall t` (BP78's `M`).
  * (BP78 Lemma 2.)  `W j ⊆ W i` for `j ≤ i`: a normal `y ≺ Ω_{j+1}` has `E_i(y) ⊆ E_j(y)`.
  * (BP78 Lemma 3.)  A normal `y ∈ Mk k` below `Ω_{k+1}` with `E_k(y) ⊆ W k` is accessible for
    `≺ ↾ Mk k` (strong induction on `k`: the predecessors of `Ω_{j+1}`, `j < k`, are handled
    at level `j`).
  * (Main lemma, BP78 (11), simultaneously in `k`.)  If `x ∈ Mall`, and `ϑ_i ξ ∈ W i` for all
    `i` and all `ξ ≺ x` with `ξ` normal, in `MM`, and `ϑ_i ξ` in the domain, then
    `ϑ_k x ∈ W k` for every `k` with `ϑ_k x` in the domain.  Induction on the length of
    `γ ≺ ϑ_k x`, `γ ∈ Mk k`.  The one new case is `γ = ϑ_k ξ` with `ξ ≺ x` and
    `E_k(ξ) ≺* ϑ_k x`, where `ξ ∈ Mall` must be shown: the levels `< k` come from `γ ∈ Mk k`,
    the level `k` from the induction on the length, and the levels `> k` by an induction on
    the length over the arguments `G_k(ξ)` (`mall_of_parts`): a coefficient `ϑ_i ζ` of level
    `i > k` has `ζ ∈ G_k(ξ)`, hence `ζ ≺ ξ ≺ x` by the domain condition of `γ`, and the
    hypothesis applies to `ζ`.  This is the only use of the domain condition.
  * `≺ ↾ MM` is well founded: its principal members are `Ω_{k+1}`, `Ω_ω` (whose predecessors
    lie below some `Ω_{k+1}`), and terms `ϑ_k a ∈ W k`; sums are handled componentwise.
  * Induction along `≺ ↾ MM` discharges the hypothesis of the main lemma; then every normal
    domain term is in `Mall`, by induction on the length.
  Hence **`WellFoundedLT ThetaVNoteD`**, for all levels and `Ω_ω` at once.
-/
import OrdinalAnalysis.Ordinal.ThetaV.Dom

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaVTerm

/-! ### Coefficients and arguments -/

/-- For `j ≤ k`, the level-`j` coefficients of a level-`k` coefficient of `α` are level-`j`
coefficients of `α`. -/
theorem mem_E_of_mem_E {j k : ℕ} (hjk : j ≤ k) :
    ∀ {a g h : ThetaVTerm}, g ∈ E k a → h ∈ E j g → h ∈ E j a
  | Omega _, _, _, hg, _ => by simp at hg
  | OmegaW, _, _, hg, _ => by simp at hg
  | theta i b, g, h, hg, hh => by
    by_cases hi : i ≤ k
    · rw [E_theta_of_le hi] at hg; simp at hg; subst hg; exact hh
    · have hki : k < i := Nat.lt_of_not_le hi
      rw [E_theta_of_lt hki] at hg
      rw [E_theta_of_lt (by omega : j < i)]
      exact mem_E_of_mem_E hjk hg hh
  | sum xs, _, _, hg, hh => by
    obtain ⟨x, hx, hg⟩ := mem_E_sum.mp hg
    exact mem_E_of_mem hx (mem_E_of_mem_E hjk hg hh)
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hx

/-- A level-`j` coefficient of level `i ≤ k ≤ j` is a level-`k` coefficient. -/
theorem mem_E_of_mem_E_of_le {i k j : ℕ} (hik : i ≤ k) (hkj : k ≤ j) :
    ∀ {a d : ThetaVTerm}, theta i d ∈ E j a → theta i d ∈ E k a
  | Omega _, _, h => by simp at h
  | OmegaW, _, h => by simp at h
  | theta i' b, d, h => by
    by_cases hi' : i' ≤ j
    · rw [E_theta_of_le hi'] at h
      simp only [List.mem_singleton, theta.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1 h2
      rw [E_theta_of_le hik]; simp
    · have hji' : j < i' := Nat.lt_of_not_le hi'
      rw [E_theta_of_lt hji'] at h
      rw [E_theta_of_lt (by omega : k < i')]
      exact mem_E_of_mem_E_of_le hik hkj h
  | sum xs, d, h => by
    obtain ⟨x, hx, hg⟩ := mem_E_sum.mp h
    exact mem_E_of_mem hx (mem_E_of_mem_E_of_le hik hkj hg)
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hx

/-- The argument of a coefficient `ϑ_i ζ` of level `i > k` is in `G_k`. -/
theorem mem_G_of_mem_E {k i j : ℕ} (hki : k < i) :
    ∀ {a d : ThetaVTerm}, theta i d ∈ E j a → d ∈ G k a
  | Omega _, _, h => by simp at h
  | OmegaW, _, h => by simp at h
  | theta i' b, d, h => by
    by_cases hi' : i' ≤ j
    · rw [E_theta_of_le hi'] at h
      simp only [List.mem_singleton, theta.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1 h2
      rw [G_theta_of_lt hki]; simp
    · have hji' : j < i' := Nat.lt_of_not_le hi'
      rw [E_theta_of_lt hji'] at h
      have hij : i ≤ j := by
        obtain ⟨j', d', hj', he⟩ := exists_eq_theta_of_mem_E h
        simp only [theta.injEq] at he
        omega
      rw [G_theta_of_lt (by omega : k < i')]
      exact List.mem_cons_of_mem _ (mem_G_of_mem_E hki h)
  | sum xs, d, h => by
    obtain ⟨x, hx, hg⟩ := mem_E_sum.mp h
    exact mem_G_sum.mpr ⟨x, hx, mem_G_of_mem_E hki hg⟩
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hx

/-- For `j ≤ k`, the level-`j` coefficients of a member of `G_k(α)` are level-`j` coefficients
of `α`. -/
theorem mem_E_of_mem_G {k j : ℕ} (hjk : j ≤ k) :
    ∀ {a z g : ThetaVTerm}, z ∈ G k a → g ∈ E j z → g ∈ E j a
  | Omega _, _, _, h, _ => by simp at h
  | OmegaW, _, _, h, _ => by simp at h
  | theta i b, z, g, h, hg => by
    by_cases hi : k < i
    · rw [G_theta_of_lt hi] at h
      rw [E_theta_of_lt (by omega : j < i)]
      rcases List.mem_cons.mp h with rfl | h
      · exact hg
      · exact mem_E_of_mem_G hjk h hg
    · rw [G_theta_of_le (Nat.le_of_not_lt hi)] at h; simp at h
  | sum xs, _, _, h, hg => by
    obtain ⟨x, hx, hz⟩ := mem_G_sum.mp h
    exact mem_E_of_mem hx (mem_E_of_mem_G hjk hz hg)
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hx

/-- `G_k` is downward closed. -/
theorem mem_G_of_mem_G {k : ℕ} : ∀ {a z y : ThetaVTerm}, z ∈ G k a → y ∈ G k z → y ∈ G k a
  | Omega _, _, _, h, _ => by simp at h
  | OmegaW, _, _, h, _ => by simp at h
  | theta i b, z, y, h, hy => by
    by_cases hi : k < i
    · rw [G_theta_of_lt hi] at h ⊢
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_of_mem _ hy
      · exact List.mem_cons_of_mem _ (mem_G_of_mem_G h hy)
    · rw [G_theta_of_le (Nat.le_of_not_lt hi)] at h; simp at h
  | sum xs, _, _, h, hy => by
    obtain ⟨x, hx, hz⟩ := mem_G_sum.mp h
    exact mem_G_sum.mpr ⟨x, hx, mem_G_of_mem_G hz hy⟩
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hx

/-- Below `Ω_{j+1}` a normal term has no coefficients of level `> j`: `E_i(y) ⊆ E_j(y)` for
`j ≤ i`. -/
theorem mem_E_of_lt_Omega {j i : ℕ} (hji : j ≤ i) :
    ∀ {y g : ThetaVTerm}, NF y → y < Omega j → g ∈ E i y → g ∈ E j y
  | Omega _, _, _, _, h => by simp at h
  | OmegaW, _, _, hy, _ => absurd hy (not_OmegaW_lt_Omega j)
  | theta i' b, _, _, hy, h => by
    have hi' := (theta_lt_Omega_iff i' j b).mp hy
    rw [E_theta_of_le (by omega : i' ≤ i)] at h
    rw [E_theta_of_le hi']; exact h
  | sum xs, _, hN, hy, h => by
    obtain ⟨x, hx, hg⟩ := mem_E_sum.mp h
    have hxs := (sum_lt_prin_iff (isPrin_Omega j) hN.desc).mp hy
    exact mem_E_of_mem hx (mem_E_of_lt_Omega hji (hN.of_mem hx) (hxs x hx) hg)
termination_by y => l y
decreasing_by exact l_lt_of_mem hx

/-! ### Accessibility, restricted to a class -/

/-- The order `≺` on normal terms, restricted to a class `S`. -/
def RelOn (S : ThetaVTerm → Prop) (a b : ThetaVTerm) : Prop := NF a ∧ S a ∧ a < b

theorem acc_of_le {S : ThetaVTerm → Prop} {a b : ThetaVTerm} (hb : Acc (RelOn S) b)
    (ha : NF a) (hS : S a) (h : a ≤ b) : Acc (RelOn S) a := by
  rcases h with h | rfl
  · exact Acc.inv hb ⟨ha, hS, h⟩
  · exact hb

/-- Accessibility for a larger class gives accessibility for a smaller one. -/
theorem acc_mono {S T : ThetaVTerm → Prop} (hST : ∀ a, S a → T a) {a : ThetaVTerm}
    (h : Acc (RelOn T) a) : Acc (RelOn S) a :=
  Subrelation.accessible (fun ⟨h1, h2, h3⟩ => ⟨h1, hST _ h2, h3⟩) h

/-- `0 = ⟨⟩` has no predecessors. -/
theorem acc_nil (S : ThetaVTerm → Prop) : Acc (RelOn S) (sum []) :=
  Acc.intro _ fun _ h => absurd h.2.2 (not_lt_nil _)

section Sums

variable (S : ThetaVTerm → Prop) (hS : ∀ xs, S (ofList xs) ↔ ∀ x ∈ xs, S x)
include hS

theorem acc_ofList_cons_aux {x : ThetaVTerm}
    (ih : ∀ x', RelOn S x' x → ∀ ys, CNF ys → (∀ y ∈ ys, S y) → (∀ y ∈ ys, y ≤ x') →
      Acc (RelOn S) (ofList ys)) :
    ∀ t, Acc (RelOn S) t → ∀ ys, ofList ys = t → Acc (RelOn S) (ofList (x :: ys)) := by
  intro t ht
  induction ht with
  | intro t _ ihA =>
  intro ys hys
  subst hys
  refine Acc.intro _ fun z ⟨hz, hSz, hlt⟩ => ?_
  have hzeq : ofList (toList z) = z := ofList_toList hz
  have hzl : CNF (toList z) := NF.cnf_toList hz
  have hSl : ∀ e ∈ toList z, S e := (hS (toList z)).mp (by rw [hzeq]; exact hSz)
  rw [← hzeq] at hlt ⊢
  rw [ofList_lt_ofList] at hlt
  generalize toList z = zs at hlt hzl hSl
  cases zs with
  | nil => exact acc_nil S
  | cons z0 zs =>
    rcases (cons_lt_cons_iff _ _ _ _).mp hlt with h | ⟨rfl, h⟩
    · exact ih z0 ⟨hzl.1 z0 List.mem_cons_self, hSl z0 List.mem_cons_self, h⟩ (z0 :: zs) hzl
        hSl hzl.le_head
    · refine ihA (ofList zs) ⟨nf_ofList_iff.mpr hzl.tail,
        (hS zs).mpr (fun e he => hSl e (List.mem_cons_of_mem _ he)),
        ofList_lt_ofList.mpr h⟩ zs rfl

theorem acc_ofList_of_le (x : ThetaVTerm) (hx : Acc (RelOn S) x) :
    ∀ ys, CNF ys → (∀ y ∈ ys, S y) → (∀ y ∈ ys, y ≤ x) → Acc (RelOn S) (ofList ys) := by
  induction hx with
  | intro x _ ihx =>
  intro ys
  induction ys with
  | nil => intro _ _ _; exact acc_nil S
  | cons y ys ihys =>
    intro hc hSy hle
    have ht : Acc (RelOn S) (ofList ys) :=
      ihys hc.tail (fun e he => hSy e (List.mem_cons_of_mem _ he))
        (fun e he => hle e (List.mem_cons_of_mem _ he))
    rcases hle y List.mem_cons_self with hlt | rfl
    · exact ihx y ⟨hc.1 y List.mem_cons_self, hSy y List.mem_cons_self, hlt⟩ (y :: ys) hc hSy
        hc.le_head
    · exact acc_ofList_cons_aux S hS ihx _ ht ys rfl

/-- A normal term whose exponents lie in `S` and are accessible for `≺` restricted to `S` is
accessible for `≺` restricted to `S`. -/
theorem acc_of_toList {t : ThetaVTerm} (ht : NF t) (hSy : ∀ y ∈ toList t, S y)
    (hA : ∀ y ∈ toList t, Acc (RelOn S) y) : Acc (RelOn S) t := by
  have hacc : Acc (RelOn S) (ofList (toList t)) := by
    cases hl : toList t with
    | nil => exact acc_nil S
    | cons y ys =>
      rw [hl] at hSy hA
      have hc : CNF (y :: ys) := hl ▸ NF.cnf_toList ht
      exact acc_ofList_of_le S hS y (hA y List.mem_cons_self) _ hc hSy hc.le_head
  rwa [ofList_toList ht] at hacc

end Sums

/-! ### The distinguished classes, bottom-up -/

/-- `Low k t`: for every `j < k`, every level-`j` coefficient `g` of `t` is in `W j`, i.e. `g`
is normal, `g ≺ Ω_{j+1}`, `g ∈ Mk j`, and `g` is accessible for `≺ ↾ Mk j` (by structural
recursion on `k`; `low_iff` is the readable form). -/
def Low : ℕ → ThetaVTerm → Prop
  | 0, _ => True
  | k + 1, t => Low k t ∧ ∀ g ∈ E k t,
      NF g ∧ g < Omega k ∧ (Dom g ∧ Low k g) ∧ Acc (RelOn (fun s => Dom s ∧ Low k s)) g

/-- BP78's `M_k`: domain terms whose coefficients of level `< k` are distinguished. -/
def Mk (k : ℕ) (t : ThetaVTerm) : Prop := Dom t ∧ Low k t

/-- BP78's `W_k`: the normal terms `≺ Ω_{k+1}` of `Mk k` accessible for `≺ ↾ Mk k`. -/
def W (k : ℕ) (t : ThetaVTerm) : Prop :=
  NF t ∧ t < Omega k ∧ Mk k t ∧ Acc (RelOn (Mk k)) t

theorem low_succ_iff {k : ℕ} {t : ThetaVTerm} :
    Low (k + 1) t ↔ Low k t ∧ ∀ g ∈ E k t, W k g := Iff.rfl

theorem low_iff {k : ℕ} {t : ThetaVTerm} : Low k t ↔ ∀ j < k, ∀ g ∈ E j t, W j g := by
  induction k with
  | zero => simp [Low]
  | succ k ih =>
    rw [low_succ_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h1 j hj
      · exact h2
    · intro h
      exact ⟨fun j hj => h j (by omega), h k (by omega)⟩

theorem Mk.anti {j k : ℕ} (hjk : j ≤ k) {t : ThetaVTerm} (h : Mk k t) : Mk j t :=
  ⟨h.1, low_iff.mpr fun i hi g hg => low_iff.mp h.2 i (by omega) g hg⟩

theorem mk_ofList_iff {k : ℕ} (xs : List ThetaVTerm) : Mk k (ofList xs) ↔ ∀ x ∈ xs, Mk k x := by
  constructor
  · rintro ⟨h1, h2⟩ x hx
    exact ⟨dom_ofList_iff.mp h1 x hx,
      low_iff.mpr fun j hj g hg => low_iff.mp h2 j hj g (mem_E_ofList.mpr ⟨x, hx, hg⟩)⟩
  · intro h
    refine ⟨dom_ofList_iff.mpr fun x hx => (h x hx).1, low_iff.mpr fun j hj g hg => ?_⟩
    obtain ⟨x, hx, hg⟩ := mem_E_ofList.mp hg
    exact low_iff.mp (h x hx).2 j hj g hg

theorem Mk.of_mem {k : ℕ} {x : ThetaVTerm} {xs : List ThetaVTerm} (h : Mk k (sum xs))
    (hx : x ∈ xs) : Mk k x :=
  ⟨h.1.of_mem hx, low_iff.mpr fun j hj g hg => low_iff.mp h.2 j hj g (mem_E_of_mem hx hg)⟩

/-- The level-`j` coefficients of a member of `W j` are in `W j`. -/
theorem W.of_mem_E {j : ℕ} {y g : ThetaVTerm} (hy : W j y) (hg : g ∈ E j y) : W j g := by
  obtain ⟨hN, _, hM, hA⟩ := hy
  have hgN : NF g := NF.of_mem_E hN hg
  have hgM : Mk j g := ⟨Dom.of_mem_E hM.1 hg, low_iff.mpr fun i hi h hh =>
    low_iff.mp hM.2 i hi h (mem_E_of_mem_E (Nat.le_of_lt hi) hg hh)⟩
  exact ⟨hgN, lt_Omega_of_mem_E hg, hgM, acc_of_le hA hgN hgM (le_of_mem_E hN hg)⟩

/-- BP78, Lemma 2: `W j ⊆ W (j + d)`. -/
theorem W.mono_add {j : ℕ} : ∀ (d : ℕ) {y : ThetaVTerm}, W j y → W (j + d) y
  | 0, _, hy => hy
  | d + 1, y, hy => by
    obtain ⟨hN, hlt, hM, hA⟩ := W.mono_add d hy
    have hlow : Low (j + d + 1) y := low_succ_iff.mpr ⟨hM.2, fun g hg =>
      W.mono_add d (hy.of_mem_E (mem_E_of_lt_Omega (by omega) hy.1 hy.2.1 hg))⟩
    exact ⟨hN, lt_trans' hlt ((Omega_lt_Omega_iff _ _).mpr (by omega)), ⟨hM.1, hlow⟩,
      acc_mono (fun _ h => Mk.anti (by omega) h) hA⟩

/-- BP78, Lemma 2: `W j ⊆ W i` for `j ≤ i`. -/
theorem W.mono {j i : ℕ} (hji : j ≤ i) {y : ThetaVTerm} (hy : W j y) : W i y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
  exact W.mono_add d hy

/-- BP78, Lemma 3, at level `k`, given the levels below. -/
theorem acc_of_E_W_aux {k : ℕ}
    (ihk : ∀ j < k, ∀ {y : ThetaVTerm}, NF y → Mk j y → y < Omega j → (∀ g ∈ E j y, W j g) →
      Acc (RelOn (Mk j)) y) :
    ∀ {y : ThetaVTerm}, NF y → Mk k y → y < Omega k → (∀ g ∈ E k y, W k g) →
      Acc (RelOn (Mk k)) y
  | Omega j, _, _, h, _ => by
    have hj := (Omega_lt_Omega_iff j k).mp h
    exact Acc.intro _ fun z ⟨hz, hMz, hlt⟩ =>
      acc_mono (fun _ h => Mk.anti (Nat.le_of_lt hj) h)
        (ihk j hj hz (Mk.anti (Nat.le_of_lt hj) hMz) hlt (fun g hg => low_iff.mp hMz.2 j hj g hg))
  | OmegaW, _, _, h, _ => absurd h (not_OmegaW_lt_Omega k)
  | theta i a, _, _, h, hE => by
    have hi := (theta_lt_Omega_iff i k a).mp h
    exact (hE _ (by rw [E_theta_of_le hi]; simp)).2.2.2
  | sum xs, hN, hM, h, hE => by
    have hxs := (sum_lt_prin_iff (isPrin_Omega k) hN.desc).mp h
    exact acc_of_toList (Mk k) mk_ofList_iff hN (fun x hx => hM.of_mem hx)
      fun x hx => acc_of_E_W_aux ihk (hN.of_mem hx) (hM.of_mem hx) (hxs x hx)
        fun g hg => hE g (mem_E_of_mem hx hg)
termination_by y => l y
decreasing_by exact l_lt_of_mem hx

/-- BP78, Lemma 3: a normal term of `Mk k` below `Ω_{k+1}` whose level-`k` coefficients are
in `W k` is accessible for `≺ ↾ Mk k`. -/
theorem acc_of_E_W (k : ℕ) : ∀ {y : ThetaVTerm}, NF y → Mk k y → y < Omega k →
    (∀ g ∈ E k y, W k g) → Acc (RelOn (Mk k)) y := by
  induction k using Nat.strong_induction_on with
  | _ k ihk => exact acc_of_E_W_aux (fun j hj => ihk j hj)

/-- Every normal term of `Mk k` below `Ω_{j+1}`, `j < k`, is accessible for `≺ ↾ Mk k`. -/
theorem acc_of_lt_Omega_low {j k : ℕ} (hjk : j < k) {z : ThetaVTerm} (hz : NF z) (hM : Mk k z)
    (hlt : z < Omega j) : Acc (RelOn (Mk k)) z :=
  acc_mono (fun _ h => Mk.anti (Nat.le_of_lt hjk) h)
    (acc_of_E_W j hz (Mk.anti (Nat.le_of_lt hjk) hM) hlt (fun g hg => low_iff.mp hM.2 j hjk g hg))

/-! ### The class `M` and the main lemma -/

/-- `Mall t`: every coefficient of every level is distinguished. -/
def Mall (t : ThetaVTerm) : Prop := ∀ j, ∀ g ∈ E j t, W j g

/-- BP78's `M`: domain terms all of whose coefficients are distinguished. -/
def MM (t : ThetaVTerm) : Prop := Dom t ∧ Mall t

/-- The hypothesis of the main lemma at `x`: the collapses, of every level, of the smaller
terms of `MM` are distinguished. -/
def Hyp (x : ThetaVTerm) : Prop :=
  ∀ ξ, NF ξ → Dom ξ → Mall ξ → ξ < x → ∀ i, Dom (theta i ξ) → W i (theta i ξ)

/-- **`Mall` from its lower part** (the only use of the domain condition): a normal domain
term whose coefficients of level `≤ k` are distinguished, and whose higher-collapse arguments
`G_k` lie below `x`, is in `Mall`, given the hypothesis of the main lemma at `x`. -/
theorem mall_of_parts {x : ThetaVTerm} (H : Hyp x) {k : ℕ} :
    ∀ {ξ : ThetaVTerm}, NF ξ → Dom ξ → (∀ j ≤ k, ∀ g ∈ E j ξ, W j g) →
      (∀ ζ ∈ G k ξ, ζ < x) → Mall ξ
  | ξ, hN, hD, hlow, hG => by
    intro j g hg
    rcases le_or_gt j k with hjk | hkj
    · exact hlow j hjk g hg
    obtain ⟨i, d, hij, rfl⟩ := exists_eq_theta_of_mem_E hg
    rcases le_or_gt i k with hik | hki
    · exact W.mono (Nat.le_of_lt hkj)
        (hlow k le_rfl _ (mem_E_of_mem_E_of_le hik (Nat.le_of_lt hkj) hg))
    · have hd : d ∈ G k ξ := mem_G_of_mem_E hki hg
      have hdN : NF d := NF.of_mem_G hN hd
      have hdD : Dom d := Dom.of_mem_G hD hd
      have hdM : Mall d := mall_of_parts H hdN hdD
        (fun j' hj' g' hg' => hlow j' hj' g' (mem_E_of_mem_G hj' hd hg'))
        (fun ζ hζ => hG ζ (mem_G_of_mem_G hd hζ))
      exact W.mono hij (H d hdN hdD hdM (hG d hd) i (Dom.of_mem_E hD hg))
termination_by ξ => l ξ
decreasing_by exact l_lt_of_mem_G hd

/-- **Main lemma** (BP78 (11), simultaneously in `k`), the induction on the length of
`γ ≺ ϑ_k x`. -/
theorem acc_of_lt_theta {x : ThetaVTerm} (hx : Mall x) (H : Hyp x) {k : ℕ} :
    ∀ {γ : ThetaVTerm}, NF γ → Mk k γ → γ < theta k x → Acc (RelOn (Mk k)) γ
  | Omega j, _, _, h => by
    have hj := (Omega_lt_theta_iff j k x).mp h
    exact Acc.intro _ fun z ⟨hz, hMz, hlt⟩ => acc_of_lt_Omega_low hj hz hMz hlt
  | OmegaW, _, _, h => absurd h (not_OmegaW_lt_theta k x)
  | theta j ξ, hγ, hM, h => by
    rcases Nat.lt_trichotomy j k with hj | rfl | hj
    · exact acc_of_lt_Omega_low hj hγ hM (theta_lt_Omega_self j ξ)
    · rcases (theta_lt_theta_iff j ξ x).mp h with ⟨h1, h2⟩ | ⟨g, hg, h3⟩
      · have hlowk : ∀ g ∈ E j ξ, W j g := fun g hg => by
          have hgN : NF g := NF.of_mem_E hγ.theta_arg hg
          have hgM : Mk j g := ⟨Dom.of_mem_E hM.1.theta_arg hg, low_iff.mpr fun i hi h hh =>
            low_iff.mp hM.2 i hi h
              (by rw [E_theta_of_lt hi]; exact mem_E_of_mem_E (Nat.le_of_lt hi) hg hh)⟩
          exact ⟨hgN, lt_Omega_of_mem_E hg, hgM, acc_of_lt_theta hx H hgN hgM (h2 g hg)⟩
        have hlow : ∀ j' ≤ j, ∀ g ∈ E j' ξ, W j' g := by
          intro j' hj' g hg
          rcases Nat.lt_or_ge j' j with hj'' | hj''
          · exact low_iff.mp hM.2 j' hj'' g (by rw [E_theta_of_lt hj'']; exact hg)
          · obtain rfl : j' = j := by omega
            exact hlowk g hg
        have hξ : Mall ξ := mall_of_parts H hγ.theta_arg hM.1.theta_arg hlow
          (fun ζ hζ => lt_trans' (hM.1.G_lt hζ) h1)
        exact (H ξ hγ.theta_arg hM.1.theta_arg hξ h1 j hM.1).2.2.2
      · exact acc_of_le (hx j g hg).2.2.2 hγ hM h3
    · exact absurd h (not_theta_lt_theta_of_lt_level ξ x hj)
  | sum xs, hγ, hM, h => by
    have hxs := (sum_lt_prin_iff (isPrin_theta k x) hγ.desc).mp h
    exact acc_of_toList (Mk k) mk_ofList_iff hγ (fun y hy => hM.of_mem hy)
      fun y hy => acc_of_lt_theta hx H (hγ.of_mem hy) (hM.of_mem hy) (hxs y hy)
termination_by γ => l γ
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · exact l_lt_of_mem hy

/-- The main lemma: `ϑ_k x ∈ W k`. -/
theorem W_theta {x : ThetaVTerm} (hN : NF x) (hx : Mall x) (H : Hyp x) {k : ℕ}
    (hD : Dom (theta k x)) : W k (theta k x) := by
  have hM : Mk k (theta k x) :=
    ⟨hD, low_iff.mpr fun j hj g hg => hx j g (by rwa [E_theta_of_lt hj] at hg)⟩
  exact ⟨(nf_theta_iff k x).mpr hN, theta_lt_Omega_self k x, hM,
    Acc.intro _ fun γ ⟨hγ, hMγ, hlt⟩ => acc_of_lt_theta hx H hγ hMγ hlt⟩

/-! ### `≺ ↾ M` is well founded -/

theorem mm_ofList_iff (xs : List ThetaVTerm) : MM (ofList xs) ↔ ∀ x ∈ xs, MM x := by
  constructor
  · rintro ⟨h1, h2⟩ x hx
    exact ⟨dom_ofList_iff.mp h1 x hx, fun j g hg => h2 j g (mem_E_ofList.mpr ⟨x, hx, hg⟩)⟩
  · intro h
    refine ⟨dom_ofList_iff.mpr fun x hx => (h x hx).1, fun j g hg => ?_⟩
    obtain ⟨x, hx, hg⟩ := mem_E_ofList.mp hg
    exact (h x hx).2 j g hg

theorem MM.of_mem {x : ThetaVTerm} {xs : List ThetaVTerm} (h : MM (sum xs)) (hx : x ∈ xs) :
    MM x :=
  ⟨h.1.of_mem hx, fun j g hg => h.2 j g (mem_E_of_mem hx hg)⟩

theorem MM.mk {t : ThetaVTerm} (h : MM t) (k : ℕ) : Mk k t :=
  ⟨h.1, low_iff.mpr fun j _ g hg => h.2 j g hg⟩

theorem acc_MM_of_lt_Omega {k : ℕ} {z : ThetaVTerm} (hz : NF z) (hM : MM z)
    (hlt : z < Omega k) : Acc (RelOn MM) z :=
  acc_mono (fun _ h => h.mk k) (acc_of_E_W k hz (hM.mk k) hlt (fun g hg => hM.2 k g hg))

/-- (Design step 4.)  `≺ ↾ MM` is well founded. -/
theorem acc_MM : ∀ {t : ThetaVTerm}, NF t → MM t → Acc (RelOn MM) t
  | Omega _, _, _ => Acc.intro _ fun _ ⟨hz, hM, hlt⟩ => acc_MM_of_lt_Omega hz hM hlt
  | OmegaW, _, _ => Acc.intro _ fun _ ⟨hz, hM, hlt⟩ => by
      obtain ⟨k, hk⟩ := exists_lt_Omega_of_lt_OmegaW hlt
      exact acc_MM_of_lt_Omega hz hM hk
  | theta k a, _, hM =>
      acc_mono (fun _ h => h.mk k) (hM.2 k _ (by rw [E_theta_of_le le_rfl]; simp)).2.2.2
  | sum xs, hN, hM =>
      acc_of_toList MM mm_ofList_iff hN (fun x hx => hM.of_mem hx)
        fun x hx => acc_MM (hN.of_mem hx) (hM.of_mem hx)
termination_by t => l t
decreasing_by exact l_lt_of_mem hx

/-- Induction along `≺ ↾ MM` discharges the hypothesis of the main lemma: `ϑ_k x ∈ W k` for
every `x ∈ MM` and every `k` with `ϑ_k x` in the domain. -/
theorem W_theta_of_MM {x : ThetaVTerm} (hN : NF x) (hM : MM x) {k : ℕ}
    (hD : Dom (theta k x)) : W k (theta k x) := by
  suffices ∀ a, Acc (RelOn MM) a → NF a → MM a → ∀ k, Dom (theta k a) → W k (theta k a) from
    this x (acc_MM hN hM) hN hM k hD
  intro a h
  induction h with
  | intro a _ ih =>
  intro hNa hMa k hD
  exact W_theta hNa hMa.2
    (fun ξ hξ hDξ hMξ hlt i hDi => ih ξ ⟨hξ, ⟨hDξ, hMξ⟩, hlt⟩ hξ ⟨hDξ, hMξ⟩ i hDi) hD

/-- (Design step 5.)  Every normal domain term is in `Mall`. -/
theorem mall_of_dom : ∀ {t : ThetaVTerm}, NF t → Dom t → Mall t
  | t, hN, hD => by
    intro j g hg
    obtain ⟨i, d, hij, rfl⟩ := exists_eq_theta_of_mem_E hg
    have hgN := NF.of_mem_E hN hg
    have hgD := Dom.of_mem_E hD hg
    have hl := l_le_of_mem_E hg
    have hdM : Mall d := mall_of_dom hgN.theta_arg hgD.theta_arg
    exact W.mono hij (W_theta_of_MM hgN.theta_arg ⟨hgD.theta_arg, hdM⟩ hgD)
termination_by t => l t
decreasing_by simp only [l_theta] at hl; omega

/-! ### Every normal domain term is accessible -/

/-- `≺` on the normal domain terms of all levels, `Ω_ω` included. -/
abbrev RelD : ThetaVTerm → ThetaVTerm → Prop := RelOn Dom

/-- **Every normal domain term is accessible.** -/
theorem accD {t : ThetaVTerm} (hN : NF t) (hD : Dom t) : Acc RelD t :=
  Subrelation.accessible (fun ⟨h1, h2, h3⟩ => ⟨h1, ⟨h2, mall_of_dom h1 h2⟩, h3⟩)
    (acc_MM hN ⟨hD, mall_of_dom hN hD⟩)

theorem wellFounded_relD : WellFounded RelD :=
  ⟨fun a => Acc.intro a fun _ ⟨hb, hD, _⟩ => accD hb hD⟩

end ThetaVTerm

namespace ThetaVNoteD

/-- Every notation is accessible. -/
theorem acc (a : ThetaVNoteD) : Acc (· < ·) a :=
  Subrelation.accessible (q := (· < ·))
    (r := InvImage ThetaVTerm.RelD Subtype.val)
    (fun {x _} h => ⟨x.2.1, x.2.2, h⟩)
    (InvImage.accessible Subtype.val (ThetaVTerm.accD a.2.1 a.2.2))

/-- **The ϑ-order with `Ω_ω` on the normal domain terms of all levels is well founded.** -/
instance wellFoundedLT : WellFoundedLT ThetaVNoteD := ⟨⟨acc⟩⟩

/-- The same, as `WellFounded`. -/
theorem wellFounded : WellFounded (α := ThetaVNoteD) (· < ·) := ⟨acc⟩

end ThetaVNoteD

end OrdinalAnalysis
