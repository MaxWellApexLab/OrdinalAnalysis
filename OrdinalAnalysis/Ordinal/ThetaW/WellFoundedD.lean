/-
  Well-foundedness of the multi-level ϑ-order on the domain terms, all levels.

  Sources: T. Arai, *Lectures on ordinal analysis*, arXiv:2304.00246, §1.6 (Definition 1.27,
  Lemma 1.29, Lemma 1.33), the distinguished-class argument, carried out level by level in the
  metatheory as in the two-level module `ThetaW/WellFounded`; the domain condition is that of
  G. Wilken, arXiv:2410.15953, Lemma 2.13 (Weiermann–Wilken, MLQ 57 (2011), Lemma 4.3), see
  `ThetaW/Dom`.

  `Rel` is `≺` restricted to the normal domain terms (`RelOn Dom`).  The predecessors of a
  domain term need not have bounded levels (`ϑ₁(Ω₆) ≺ Ω₂`, `ThetaW/Dom`), so the argument is
  organised by the interval `[Ω_b, Ω_{b+1})` of the term, by induction on `b`.

  * (Skeleton.)  `Sk b N t`: every `Ω_{j+1}` and `ϑ_j` reached from `t` through sums and through
    the collapses of level `≥ b` has `j < N`; the collapses of level `< b` are atoms.  `Sk 0 N`
    is the level bound `LevLT N`.
  * (Skeleton closure, the one place where the domain condition is used.)  If `t ≺ Ω_{b+1}`
    (`t < Omega b`), `Sk b N t`, `b < N`, and `s ≼ t` is normal and in the domain, then
    `Sk b N s`.  The exponents of `s` are below those of `t`; for `ϑ_b γ ≼ ϑ_b α` either
    `ϑ_b γ ≼ δ` for some `δ ∈ E_b(α)` (recursion), or `γ ≺ α` and `E_b(γ) ≺* ϑ_b α`: then
    `γ ≺ α ≺ ϑ_N 0`, the arguments `G_b(γ)` of the higher collapses in `γ` are `≺ γ` by the
    domain condition, and the level-`b` members of `E_b(γ)` are below `ϑ_b α` (recursion).
    In particular (`b = 0`) the predecessors of a countable domain term with levels `< N` have
    levels `< N`.
  * (Top-down, base `b`, top level `N - 1 = b + M`.)  `Cls 0 = Dom ∩ Sk b N`,
    `Cls (i+1) = {t ∈ Cls i | E_{b+i}(t) ⊆ Acc(≺ ↾ Cls i)}`; so `Cls (i+1)` is Arai's `D_{b+i}`
    and `W_{b+i} = Acc(≺ ↾ Cls i)`.  Given that every domain term below `Ω_b` is accessible
    (the induction hypothesis on `b`):
    - `Cls i ∩ Ω_{b+i} ⊆ W_{b+i}` for all `i` (bottom-up), and `Cls (i+1) ∩ Ω_{b+i+1} ⊆ W_{b+i}`
      (Arai, Lemma 1.29 at level `b + i`);
    - main lemma (Arai, Lemma 1.33 for `ϑ_{b+i}`): if `α ∈ Cls (i+1)` and `ϑ_{b+i} ξ ∈ W_{b+i}`
      for all `ξ ∈ Cls (i+1)` below `α`, then `ϑ_{b+i} α ∈ W_{b+i}`;
    - `≺ ↾ Cls (M+1)` is well founded (at the top level, a term above `Ω_{b+M+1}` is a sum of
      shorter terms, by the skeleton bound), and from `≺ ↾ Cls (i+2)` well founded follows
      `ϑ_{b+i+1}` maps `Cls (i+2)` into `W_{b+i+1}`, hence `Cls (i+1) ⊆ Cls (i+2)`, hence
      `≺ ↾ Cls (i+1)` well founded;
    - at the bottom, `ϑ_b` maps `Cls 1` into `W_b`, and every term of `Cls 0` below `Ω_{b+1}` is
      in `W_b` (induction on the length).
    By the skeleton closure, accessibility for `≺ ↾ Cls 0` gives accessibility for `Rel`.
  * Every term lies below some `Ω_{n+1}`, so every normal domain term is accessible:
    **`WellFoundedLT ThetaWNoteD`**, for all levels at once.
-/
import OrdinalAnalysis.Ordinal.ThetaW.Dom
import OrdinalAnalysis.Ordinal.ThetaW.WellFounded

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

/-! ### The skeleton above level `b` -/

mutual
/-- `Sk b N t`: every `Ω_{j+1}` and `ϑ_j` reached from `t` through sums and through collapses
of level `≥ b` has `j < N`. -/
def Sk (b N : ℕ) : ThetaWTerm → Prop
  | Omega k => k < N
  | theta k a => k < N ∧ (b ≤ k → Sk b N a)
  | sum xs => SkList b N xs
/-- Every entry of the list satisfies `Sk b N`. -/
def SkList (b N : ℕ) : List ThetaWTerm → Prop
  | [] => True
  | x :: xs => Sk b N x ∧ SkList b N xs
end

section Skeleton

variable {b N : ℕ}

@[simp] theorem sk_Omega (k : ℕ) : Sk b N (Omega k) ↔ k < N := by simp [Sk]

theorem sk_theta (k : ℕ) (a : ThetaWTerm) : Sk b N (theta k a) ↔ k < N ∧ (b ≤ k → Sk b N a) := by
  simp [Sk]

theorem skList_iff {xs : List ThetaWTerm} : SkList b N xs ↔ ∀ x ∈ xs, Sk b N x := by
  induction xs with
  | nil => simp [SkList]
  | cons y ys ih => simp [SkList, ih]

theorem sk_sum_iff (xs : List ThetaWTerm) : Sk b N (sum xs) ↔ ∀ x ∈ xs, Sk b N x := by
  simp only [Sk, skList_iff]

theorem sk_ofList_iff {xs : List ThetaWTerm} : Sk b N (ofList xs) ↔ ∀ x ∈ xs, Sk b N x := by
  match xs with
  | [] => simp [sk_sum_iff]
  | [x] =>
    by_cases h : IsPrin x
    · rw [ofList_singleton_prin h]; simp
    · rw [ofList_singleton_not_prin h]; exact sk_sum_iff [x]
  | _ :: _ :: _ => exact sk_sum_iff _

theorem Sk.of_mem {x : ThetaWTerm} {xs : List ThetaWTerm} (h : Sk b N (sum xs)) (hx : x ∈ xs) :
    Sk b N x :=
  (sk_sum_iff xs).mp h x hx

theorem Sk.theta_arg {k : ℕ} {a : ThetaWTerm} (h : Sk b N (theta k a)) (hk : b ≤ k) :
    Sk b N a :=
  ((sk_theta k a).mp h).2 hk

/-- A collapse of level `< b` is an atom of the skeleton. -/
theorem sk_theta_of_lt {k : ℕ} (a : ThetaWTerm) (hk : k < b) (hbN : b ≤ N) :
    Sk b N (theta k a) :=
  (sk_theta k a).mpr ⟨by omega, fun h => absurd h (Nat.not_le.mpr hk)⟩

/-- The level-`k` coefficients (`k ≥ b`) inherit the skeleton bound. -/
theorem Sk.of_mem_E {k : ℕ} (hbk : b ≤ k) : ∀ {a g : ThetaWTerm}, Sk b N a → g ∈ E k a → Sk b N g
  | Omega _, g, _, h => by simp at h
  | theta j a, g, ha, h => by
    by_cases hj : j ≤ k
    · rw [E_theta_of_le hj] at h; simp at h; exact h ▸ ha
    · have hkj : k < j := Nat.lt_of_not_le hj
      rw [E_theta_of_lt hkj] at h
      exact Sk.of_mem_E hbk (ha.theta_arg (by omega)) h
  | sum xs, g, ha, h => by
    obtain ⟨x, hx, hg⟩ := mem_E_sum.mp h
    exact Sk.of_mem_E hbk (ha.of_mem hx) hg
termination_by a => l a
decreasing_by
  · simp
  · exact l_lt_of_mem hx

/-- A level bound gives the skeleton bound. -/
theorem Sk.of_levLT : ∀ {t : ThetaWTerm}, LevLT N t → Sk b N t
  | Omega k, h => by simpa using h
  | theta k a, h => by
    rw [levLT_theta] at h
    exact (sk_theta k a).mpr ⟨h.1, fun _ => Sk.of_levLT h.2⟩
  | sum xs, h => by
    rw [levLT_sum_iff] at h
    exact (sk_sum_iff xs).mpr fun x hx => Sk.of_levLT (h x hx)
termination_by t => l t
decreasing_by
  · simp
  · exact l_lt_of_mem hx

/-- For `b = 0` the skeleton bound is the level bound. -/
theorem sk_zero_iff_levLT : ∀ {t : ThetaWTerm}, Sk 0 N t ↔ LevLT N t
  | Omega k => by simp
  | theta k a => by
    rw [sk_theta, levLT_theta, sk_zero_iff_levLT (t := a)]
    exact ⟨fun h => ⟨h.1, h.2 (Nat.zero_le k)⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
  | sum xs => by
    rw [sk_sum_iff, levLT_sum_iff]
    exact ⟨fun h x hx => (sk_zero_iff_levLT (t := x)).mp (h x hx),
      fun h x hx => (sk_zero_iff_levLT (t := x)).mpr (h x hx)⟩
termination_by t => l t
decreasing_by
  · simp
  · exact l_lt_of_mem hx
  · exact l_lt_of_mem hx

/-- A term with skeleton bound `N` lies below `ϑ_N 0`. -/
theorem Sk.lt_theta_zero : ∀ {t : ThetaWTerm}, Sk b N t → t < theta N zero
  | Omega k, h => (Omega_lt_theta_iff k N _).mpr ((sk_Omega k).mp h)
  | theta k a, h => theta_lt_theta_of_lt_level a zero ((sk_theta k a).mp h).1
  | sum [], _ => nil_lt_theta N _
  | sum (x :: xs), h =>
    (cons_lt_theta_iff N x zero xs).mpr (Sk.lt_theta_zero (h.of_mem List.mem_cons_self))
termination_by t => l t
decreasing_by simp; omega

theorem Omega_lt_theta_zero_iff {j : ℕ} : Omega j < theta N zero ↔ j < N :=
  Omega_lt_theta_iff j N zero

theorem lt_level_of_theta_lt_theta_zero {j : ℕ} {a : ThetaWTerm} (h : theta j a < theta N zero) :
    j < N := by
  rcases Nat.lt_trichotomy j N with hj | rfl | hj
  · exact hj
  · rcases (theta_lt_theta_iff j a zero).mp h with ⟨h1, _⟩ | ⟨g, hg, _⟩
    · exact absurd h1 (not_lt_nil a)
    · simp [zero] at hg
  · exact absurd h (not_theta_lt_theta_of_lt_level a zero hj)

/-- The skeleton bound from its parts: a normal term below `ϑ_N 0` whose higher-collapse
arguments `G_b` lie below `ϑ_N 0` and whose level-`b` coefficients have skeleton bound `N`. -/
theorem Sk.of_parts (hbN : b < N) : ∀ {x : ThetaWTerm}, NF x → x < theta N zero →
    (∀ y ∈ G b x, y < theta N zero) → (∀ δ ∈ E b x, Sk b N δ) → Sk b N x
  | Omega j, _, h, _, _ => (sk_Omega j).mpr (Omega_lt_theta_zero_iff.mp h)
  | theta j y, hx, h, hG, hE => by
    have hjN := lt_level_of_theta_lt_theta_zero h
    by_cases hj : b < j
    · refine (sk_theta j y).mpr ⟨hjN, fun _ => ?_⟩
      rw [G_theta_of_lt hj] at hG
      rw [E_theta_of_lt hj] at hE
      exact Sk.of_parts hbN hx.theta_arg (hG y List.mem_cons_self)
        (fun z hz => hG z (List.mem_cons_of_mem y hz)) hE
    · exact hE _ (by rw [E_theta_of_le (Nat.le_of_not_lt hj)]; simp)
  | sum xs, hx, h, hG, hE => by
    have hxs := (sum_lt_prin_iff (isPrin_theta N zero) hx.desc).mp h
    refine (sk_sum_iff xs).mpr fun z hz => ?_
    exact Sk.of_parts hbN (hx.of_mem hz) (hxs z hz)
      (fun y hy => hG y (mem_G_sum.mpr ⟨z, hz, hy⟩)) (fun d hd => hE d (mem_E_of_mem hz hd))
termination_by x => l x
decreasing_by
  · simp
  · exact l_lt_of_mem hz

/-- **Skeleton closure.**  Below `Ω_{b+1}`, the normal domain terms `≼ t` inherit the skeleton
bound of `t`.  This is where the domain condition is used. -/
theorem Sk.of_le_aux (hbN : b < N) (n : ℕ) :
    ∀ s t : ThetaWTerm, l s + l t ≤ n → NF s → Dom s → Sk b N t → t < Omega b → s ≤ t →
      Sk b N s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s t hn hs hD hSk ht hst
  have IH : ∀ {s' t' : ThetaWTerm}, l s' + l t' < l s + l t → NF s' → Dom s' → Sk b N t' →
      t' < Omega b → s' ≤ t' → Sk b N s' :=
    fun h => ih _ (by omega) _ _ le_rfl
  have hsb : s < Omega b := lt_of_le_of_lt' hst ht
  cases s with
  | Omega j =>
    have := (Omega_lt_Omega_iff j b).mp hsb
    exact (sk_Omega j).mpr (by omega)
  | theta j γ =>
    have hjb := (theta_lt_Omega_iff j b γ).mp hsb
    rcases Nat.lt_or_ge j b with hj | hj
    · exact sk_theta_of_lt γ hj (Nat.le_of_lt hbN)
    obtain rfl : j = b := by omega
    cases t with
    | Omega i =>
      have hi := (Omega_lt_Omega_iff i j).mp ht
      rcases hst with h | h
      · have := (theta_lt_Omega_iff j i γ).mp h; omega
      · cases h
    | sum ts =>
      cases ts with
      | nil =>
        rcases hst with h | h
        · exact absurd h (not_theta_lt_nil j γ)
        · cases h
      | cons p ps =>
        have hp : theta j γ ≤ p := by
          rcases hst with h | h
          · exact (theta_lt_cons_iff j γ p ps).mp h
          · cases h
        exact IH (by simp; omega) hs hD (hSk.of_mem List.mem_cons_self)
          ((cons_lt_Omega_iff j p ps).mp ht) hp
    | theta i α =>
      have hij : i ≤ j := (theta_lt_Omega_iff i j α).mp ht
      rcases hst with hlt | heq
      swap
      · rw [heq]; exact hSk
      rcases Nat.lt_or_ge i j with hi | hi
      · exact absurd hlt (not_theta_lt_theta_of_lt_level γ α hi)
      obtain rfl : i = j := by omega
      have hSkα : Sk i N α := hSk.theta_arg le_rfl
      rcases (theta_lt_theta_iff i γ α).mp hlt with ⟨h1, h2⟩ | ⟨g, hg, h3⟩
      · refine (sk_theta i γ).mpr ⟨hbN, fun _ => ?_⟩
        have hγB : γ < theta N zero := lt_trans' h1 hSkα.lt_theta_zero
        refine Sk.of_parts hbN hs.theta_arg hγB (fun y hy => lt_trans' (hD.G_lt hy) hγB)
          fun δ hδ => ?_
        obtain ⟨j', d, hj', rfl⟩ := exists_eq_theta_of_mem_E hδ
        rcases Nat.lt_or_ge j' i with hj'' | hj''
        · exact sk_theta_of_lt d hj'' (Nat.le_of_lt hbN)
        obtain rfl : j' = i := by omega
        have := l_le_of_mem_E hδ
        exact IH (by simp at this ⊢; omega) (NF.of_mem_E hs.theta_arg hδ)
          (Dom.of_mem_E hD.theta_arg hδ)
          hSk ht (Or.inl (h2 _ hδ))
      · have := l_le_of_mem_E hg
        exact IH (by simp; omega) hs hD (Sk.of_mem_E le_rfl hSkα hg) (lt_Omega_of_mem_E hg) h3
  | sum xs =>
    refine (sk_sum_iff xs).mpr fun x hx => ?_
    have hxN := hs.of_mem hx
    have hxD := hD.of_mem hx
    have hl := l_lt_of_mem hx
    cases xs with
    | nil => cases hx
    | cons c cs =>
    have hxc : x ≤ c := hs.desc.le_head x hx
    rcases shape t with hp | rfl | ⟨p, ps, rfl⟩
    · have hst' : sum (c :: cs) < t := by
        rcases hst with h | h
        · exact h
        · exact absurd (h ▸ hp) (not_isPrin_sum _)
      have hct : c < t := (cons_lt_prin_iff hp).mp hst'
      exact IH (by omega) hxN hxD hSk ht (Or.inl (lt_of_le_of_lt' hxc hct))
    · rcases hst with h | h
      · exact absurd h (not_lt_nil _)
      · cases h
    · have hcp : c ≤ p := by
        rcases hst with h | h
        · rcases (cons_lt_cons_iff c p cs ps).mp h with h | ⟨h, _⟩
          · exact Or.inl h
          · exact Or.inr h
        · cases h; exact le_refl' _
      have hpl := l_lt_of_mem (xs := p :: ps) List.mem_cons_self
      exact IH (by omega) hxN hxD (hSk.of_mem List.mem_cons_self)
        ((cons_lt_Omega_iff b p ps).mp ht) (le_trans' hxc hcp)

theorem Sk.of_le (hbN : b < N) {s t : ThetaWTerm} (hs : NF s) (hD : Dom s) (hSk : Sk b N t)
    (ht : t < Omega b) (hst : s ≤ t) : Sk b N s :=
  Sk.of_le_aux hbN _ s t le_rfl hs hD hSk ht hst

end Skeleton

/-- The predecessors of a countable normal domain term all of whose levels are `< N` have all
their levels `< N`. -/
theorem levLT_of_lt_of_lt_Omega0 {N : ℕ} (hN : 0 < N) {s t : ThetaWTerm} (hs : NF s)
    (hD : Dom s) (hL : LevLT N t) (ht : t < Omega 0) (hst : s < t) : LevLT N s :=
  sk_zero_iff_levLT.mp (Sk.of_le hN hs hD (sk_zero_iff_levLT.mpr hL) ht (Or.inl hst))

/-! ### The distinguished classes above a base level `b` -/

/-- `Cls b N 0 = Dom ∩ Sk b N`; `Cls b N (i+1)`: the terms of `Cls b N i` whose level-`(b+i)`
coefficients are accessible for `≺` restricted to `Cls b N i` (Arai's `D_{b+i}`). -/
def Cls (b N : ℕ) : ℕ → ThetaWTerm → Prop
  | 0 => fun t => Dom t ∧ Sk b N t
  | i + 1 => fun t => Cls b N i t ∧ ∀ g ∈ E (b + i) t, Acc (RelOn (Cls b N i)) g

/-- `t` lies below `Ω_c` (`BelowΩ 0` is empty; `BelowΩ (c+1) t` is `t < Omega c`). -/
def BelowΩ : ℕ → ThetaWTerm → Prop
  | 0, _ => False
  | c + 1, t => t < Omega c

section Classes

variable {b N : ℕ}

theorem cls_zero_iff {t : ThetaWTerm} : Cls b N 0 t ↔ Dom t ∧ Sk b N t := Iff.rfl

theorem cls_succ_iff {i : ℕ} {t : ThetaWTerm} :
    Cls b N (i + 1) t ↔ Cls b N i t ∧ ∀ g ∈ E (b + i) t, Acc (RelOn (Cls b N i)) g := Iff.rfl

theorem Cls.pred {i : ℕ} {t : ThetaWTerm} (h : Cls b N (i + 1) t) : Cls b N i t := h.1

theorem Cls.to_zero : ∀ {i : ℕ} {t : ThetaWTerm}, Cls b N i t → Cls b N 0 t
  | 0, _, h => h
  | _ + 1, _, h => Cls.to_zero h.1

theorem cls_ofList_iff : ∀ (i : ℕ) (xs : List ThetaWTerm),
    Cls b N i (ofList xs) ↔ ∀ x ∈ xs, Cls b N i x
  | 0, xs => by
    rw [cls_zero_iff, dom_ofList_iff, sk_ofList_iff]
    exact ⟨fun h x hx => ⟨h.1 x hx, h.2 x hx⟩, fun h => ⟨fun x hx => (h x hx).1,
      fun x hx => (h x hx).2⟩⟩
  | i + 1, xs => by
    rw [cls_succ_iff, cls_ofList_iff i xs]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      exact ⟨h1 x hx, fun g hg => h2 g (mem_E_ofList.mpr ⟨x, hx, hg⟩)⟩
    · intro h
      refine ⟨fun x hx => (h x hx).1, fun g hg => ?_⟩
      obtain ⟨x, hx, hg⟩ := mem_E_ofList.mp hg
      exact (h x hx).2 g hg

theorem Cls.of_mem : ∀ {i : ℕ} {x : ThetaWTerm} {xs : List ThetaWTerm}, Cls b N i (sum xs) →
    x ∈ xs → Cls b N i x
  | 0, _, _, h, hx => ⟨h.1.of_mem hx, h.2.of_mem hx⟩
  | _ + 1, _, _, h, hx => ⟨Cls.of_mem h.1 hx, fun g hg => h.2 g (mem_E_of_mem hx hg)⟩

/-- The level-`k` coefficients (`k ≥ b + i`) of a term of `Cls i` are in `Cls i`. -/
theorem Cls.of_mem_E : ∀ {i k : ℕ} {t g : ThetaWTerm}, b + i ≤ k → Cls b N i t → g ∈ E k t →
    Cls b N i g
  | 0, _, _, _, hk, h, hg => ⟨Dom.of_mem_E h.1 hg, Sk.of_mem_E (by omega) h.2 hg⟩
  | i + 1, _, _, _, hk, h, hg =>
    ⟨Cls.of_mem_E (by omega) h.1 hg, fun _ hd => h.2 _ (mem_E_of_mem_E (by omega) hg hd)⟩

/-- `Cls i` passes from `ϑ_j ξ` to `ξ` for `j ≥ b + i`. -/
theorem Cls.theta_arg : ∀ {i j : ℕ} {ξ : ThetaWTerm}, b + i ≤ j → Cls b N i (theta j ξ) →
    Cls b N i ξ
  | 0, _, _, hj, h => ⟨h.1.theta_arg, h.2.theta_arg (by omega)⟩
  | i + 1, j, ξ, hj, h =>
    ⟨Cls.theta_arg (by omega) h.1,
      fun g hg => h.2 g (by rw [E_theta_of_lt (by omega : b + i < j)]; exact hg)⟩

/-! ### Below `Ω_{b+i}` -/

/-- `HLow i`: every term of `Cls i` below `Ω_{b+i}` is in `W_{b+i} = Acc(≺ ↾ Cls i)`. -/
def HLow (b N i : ℕ) : Prop :=
  ∀ t, NF t → Cls b N i t → BelowΩ (b + i) t → Acc (RelOn (Cls b N i)) t

theorem belowΩ_of_Omega_lt {c : ℕ} {t : ThetaWTerm} {j : ℕ} (hj : j < c) (h : t < Omega j) :
    BelowΩ c t := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  show t < Omega c'
  rcases Nat.lt_or_ge j c' with h' | h'
  · exact lt_trans' h ((Omega_lt_Omega_iff j c').mpr h')
  · obtain rfl : j = c' := by omega
    exact h

theorem belowΩ_theta {c j : ℕ} (hj : j < c) (a : ThetaWTerm) : BelowΩ c (theta j a) := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  exact (theta_lt_Omega_iff j c' a).mpr (by omega)

/-- `Ω_{j+1} ∈ W_{b+i}` for `j + 1 ≤ b + i`. -/
theorem acc_Omega_of_hLow {i j : ℕ} (hL : HLow b N i) (hj : j < b + i) :
    Acc (RelOn (Cls b N i)) (Omega j) :=
  Acc.intro _ fun s ⟨hs, hC, hlt⟩ => hL s hs hC (belowΩ_of_Omega_lt hj hlt)

/-- Arai, Lemma 1.29 at level `b + i`: `Cls (i+1) ∩ Ω_{b+i+1} ⊆ W_{b+i}`. -/
theorem acc_of_lt_Omega {i : ℕ} (hL : HLow b N i) :
    ∀ {t : ThetaWTerm}, NF t → Cls b N (i + 1) t → t < Omega (b + i) → Acc (RelOn (Cls b N i)) t
  | Omega j, _, _, h => acc_Omega_of_hLow hL ((Omega_lt_Omega_iff j _).mp h)
  | theta j ξ, _, hC, h => by
    have := (theta_lt_Omega_iff j _ ξ).mp h
    exact hC.2 (theta j ξ) (by rw [E_theta_of_le this]; simp)
  | sum xs, ht, hC, hlt => by
    have hxs : ∀ x ∈ xs, x < Omega (b + i) := (sum_lt_prin_iff (isPrin_Omega _) ht.desc).mp hlt
    exact acc_of_toList (Cls b N i) (cls_ofList_iff i) ht (fun x hx => (hC.of_mem hx).1)
      fun x hx => acc_of_lt_Omega hL (ht.of_mem hx) (hC.of_mem hx) (hxs x hx)
termination_by t => l t
decreasing_by exact l_lt_of_mem hx

theorem hLow_succ {i : ℕ} (hL : HLow b N i) : HLow b N (i + 1) :=
  fun _ ht hC hB => acc_mono (fun _ h => h.1) (acc_of_lt_Omega hL ht hC hB)

theorem hLow_all (h0 : HLow b N 0) : ∀ i, HLow b N i
  | 0 => h0
  | i + 1 => hLow_succ (hLow_all h0 i)

/-! ### The main lemma at level `b + i` (Arai, Lemma 1.33) -/

/-- The induction on the length of `γ ≺ ϑ_{b+i} α` in the main lemma. -/
theorem acc_of_lt_theta {i : ℕ} (hL : HLow b N i) {α : ThetaWTerm} (hM : Cls b N (i + 1) α)
    (hyp : ∀ ξ, NF ξ → Cls b N (i + 1) ξ → ξ < α → Acc (RelOn (Cls b N i)) (theta (b + i) ξ)) :
    ∀ {γ : ThetaWTerm}, NF γ → Cls b N i γ → γ < theta (b + i) α → Acc (RelOn (Cls b N i)) γ
  | Omega j, _, _, h => acc_Omega_of_hLow hL ((Omega_lt_theta_iff j _ α).mp h)
  | theta j ξ, hγ, hC, h => by
    rcases Nat.lt_trichotomy j (b + i) with hj | hj | hj
    · exact hL _ hγ hC (belowΩ_theta hj ξ)
    · subst hj
      rcases (theta_lt_theta_iff _ ξ α).mp h with ⟨h1, h2⟩ | ⟨g, hg, h3⟩
      · have hξ : Cls b N i ξ := hC.theta_arg le_rfl
        refine hyp ξ hγ.theta_arg ⟨hξ, fun g hg => ?_⟩ h1
        exact acc_of_lt_theta hL hM hyp (NF.of_mem_E hγ.theta_arg hg)
          (hξ.of_mem_E le_rfl hg) (h2 g hg)
      · exact acc_of_le (hM.2 g hg) hγ hC h3
    · exact absurd h (not_theta_lt_theta_of_lt_level ξ α hj)
  | sum xs, hγ, hC, h => by
    have hxs : ∀ x ∈ xs, x < theta (b + i) α :=
      (sum_lt_prin_iff (isPrin_theta _ α) hγ.desc).mp h
    exact acc_of_toList (Cls b N i) (cls_ofList_iff i) hγ (fun x hx => hC.of_mem hx) fun x hx =>
      acc_of_lt_theta hL hM hyp (hγ.of_mem hx) (hC.of_mem hx) (hxs x hx)
termination_by γ => l γ
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · exact l_lt_of_mem hx

/-- `Result i`: `≺` restricted to `Cls (i+1)` is well founded on `Cls (i+1)`. -/
def Result (b N i : ℕ) : Prop :=
  ∀ t, NF t → Cls b N (i + 1) t → Acc (RelOn (Cls b N (i + 1))) t

/-- `ϑ_{b+i}` maps `Cls (i+1)` into `W_{b+i}`, by induction along `≺ ↾ Cls (i+1)`. -/
theorem acc_theta {i : ℕ} (hL : HLow b N i) (hR : Result b N i) {α : ThetaWTerm} (hα : NF α)
    (hM : Cls b N (i + 1) α) : Acc (RelOn (Cls b N i)) (theta (b + i) α) := by
  suffices ∀ a, Acc (RelOn (Cls b N (i + 1))) a → NF a → Cls b N (i + 1) a →
      Acc (RelOn (Cls b N i)) (theta (b + i) a) from this α (hR α hα hM) hα hM
  intro a h
  induction h with
  | intro a _ ih =>
  intro _ hMa
  exact Acc.intro _ fun _ ⟨hγ, hCγ, hlt⟩ =>
    acc_of_lt_theta hL hMa (fun ξ hξ hMξ hlt' => ih ξ ⟨hξ, hMξ, hlt'⟩ hξ hMξ) hγ hCγ hlt

/-- Collapse of the class: `Cls (i+1) ⊆ Cls (i+2)`, given that `ϑ_{b+i+1}` maps `Cls (i+2)`
into `W_{b+i+1}`. -/
theorem cls_succ_of_cls {i : ℕ} (hL : HLow b N (i + 1))
    (hθ : ∀ α, NF α → Cls b N (i + 2) α → Acc (RelOn (Cls b N (i + 1))) (theta (b + (i + 1)) α)) :
    ∀ (n : ℕ) {t : ThetaWTerm}, l t ≤ n → NF t → Cls b N (i + 1) t → Cls b N (i + 2) t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t hn ht hC
  refine ⟨hC, fun g hg => ?_⟩
  have hgC : Cls b N (i + 1) g := hC.of_mem_E le_rfl hg
  have hgN : NF g := NF.of_mem_E ht hg
  have hgl := l_le_of_mem_E hg
  obtain ⟨j, d, hj, rfl⟩ := exists_eq_theta_of_mem_E hg
  rcases Nat.lt_or_ge j (b + (i + 1)) with hj' | hj'
  · exact hL _ hgN hgC (belowΩ_theta hj' d)
  · obtain rfl : j = b + (i + 1) := by omega
    simp only [l_theta] at hgl
    exact hθ d hgN.theta_arg (ih (l d) (by omega) le_rfl hgN.theta_arg (hgC.theta_arg le_rfl))

/-- The step of the top-down recursion: `Result (i+1) → Result i`. -/
theorem result_of_succ {i : ℕ} (hL : HLow b N (i + 1)) (hR : Result b N (i + 1)) :
    Result b N i := by
  have hθ := fun α (hα : NF α) (hM : Cls b N (i + 2) α) => acc_theta hL hR hα hM
  intro t ht hC
  suffices ∀ a, Acc (RelOn (Cls b N (i + 2))) a → Acc (RelOn (Cls b N (i + 1))) a from
    this t (hR t ht (cls_succ_of_cls hL hθ _ le_rfl ht hC))
  intro a h
  induction h with
  | intro a _ ih =>
  exact Acc.intro _ fun z ⟨hz, hCz, hlt⟩ =>
    ih z ⟨hz, cls_succ_of_cls hL hθ _ le_rfl hz hCz, hlt⟩

/-- The top level `b + M`: above `Ω_{b+M+1}` a term of the skeleton bound `b + M + 1` is a
sum of shorter terms. -/
theorem result_top {M : ℕ} (hL : HLow b (b + M + 1) M) : Result b (b + M + 1) M := by
  intro t
  induction t using (measure l).wf.induction with
  | _ t ih =>
  intro ht hC
  have base : ∀ {s : ThetaWTerm}, NF s → Cls b (b + M + 1) (M + 1) s → s < Omega (b + M) →
      Acc (RelOn (Cls b (b + M + 1) (M + 1))) s :=
    fun hs hCs hlt => acc_mono (fun _ h => h.1) (acc_of_lt_Omega hL hs hCs hlt)
  rcases lt_trichotomy' t (Omega (b + M)) with h | rfl | h
  · exact base ht hC h
  · exact Acc.intro _ fun _ ⟨hz, hCz, hlt⟩ => base hz hCz hlt
  · have hSk : Sk b (b + M + 1) t := (Cls.to_zero hC).2
    rcases Omega_lt_iff.mp h with ⟨hp, hk⟩ | ⟨c, cs, rfl, _⟩
    · exfalso
      cases t with
      | sum _ => exact hp
      | Omega j => simp at hk hSk; omega
      | theta j a => simp at hk; have := ((sk_theta j a).mp hSk).1; omega
    · refine acc_of_toList (Cls b (b + M + 1) (M + 1)) (cls_ofList_iff (M + 1)) ht
        (fun x hx => hC.of_mem hx) fun x hx => ?_
      exact ih x (l_lt_of_mem hx) (ht.of_mem hx) (hC.of_mem hx)

/-- The top-down recursion: `Result i` for every `i ≤ M`. -/
theorem result_all {M : ℕ} (h0 : HLow b (b + M + 1) 0) : ∀ d, d ≤ M → Result b (b + M + 1) (M - d)
  | 0, _ => result_top (hLow_all h0 M)
  | d + 1, hd => by
    have hR := result_all h0 d (by omega)
    have e : M - d = (M - (d + 1)) + 1 := by omega
    rw [e] at hR
    exact result_of_succ (hLow_all h0 _) hR

/-- At the base level `b`: every term of `Cls 0` below `Ω_{b+1}` is in `W_b`. -/
theorem acc_cls0_of_lt_Omega {M : ℕ} (h0 : HLow b (b + M + 1) 0) :
    ∀ {t : ThetaWTerm}, NF t → Cls b (b + M + 1) 0 t → t < Omega b →
      Acc (RelOn (Cls b (b + M + 1) 0)) t
  | Omega j, _, _, h => acc_Omega_of_hLow h0 ((Omega_lt_Omega_iff j b).mp h)
  | theta j ξ, ht, hC, h => by
    have hjb := (theta_lt_Omega_iff j b ξ).mp h
    rcases Nat.lt_or_ge j b with hj | hj
    · exact h0 _ ht hC (belowΩ_theta hj ξ)
    have e : b = j := by omega
    subst e
    have hR : Result b (b + M + 1) 0 := by
      have := result_all h0 M le_rfl
      rwa [Nat.sub_self] at this
    refine acc_theta h0 hR ht.theta_arg ⟨hC.theta_arg le_rfl, fun g hg => ?_⟩
    exact acc_cls0_of_lt_Omega h0 (NF.of_mem_E ht.theta_arg hg)
      ((hC.theta_arg le_rfl).of_mem_E le_rfl hg) (lt_Omega_of_mem_E hg)
  | sum xs, ht, hC, h => by
    have hxs : ∀ x ∈ xs, x < Omega b := (sum_lt_prin_iff (isPrin_Omega _) ht.desc).mp h
    exact acc_of_toList (Cls b (b + M + 1) 0) (cls_ofList_iff 0) ht (fun x hx => hC.of_mem hx)
      fun x hx => acc_cls0_of_lt_Omega h0 (ht.of_mem hx) (hC.of_mem hx) (hxs x hx)
termination_by t => l t
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · exact l_lt_of_mem hx

end Classes

/-! ### Every normal domain term is accessible -/

/-- `≺` on the normal domain terms of all levels. -/
abbrev RelD : ThetaWTerm → ThetaWTerm → Prop := RelOn Dom

/-- Accessibility for `≺ ↾ Cls 0` below `Ω_{b+1}` is accessibility for `≺` on all normal
domain terms, by the skeleton closure. -/
theorem accD_of_acc_cls0 {b N : ℕ} (hbN : b < N) :
    ∀ t, Acc (RelOn (Cls b N 0)) t → NF t → Cls b N 0 t → t < Omega b → Acc RelD t := by
  intro t h
  induction h with
  | intro t _ ih =>
  intro _ hC ht
  exact Acc.intro _ fun s ⟨hs, hD, hlt⟩ =>
    ih s ⟨hs, ⟨hD, Sk.of_le hbN hs hD hC.2 ht (Or.inl hlt)⟩, hlt⟩ hs
      ⟨hD, Sk.of_le hbN hs hD hC.2 ht (Or.inl hlt)⟩ (lt_trans' hlt ht)

/-- Every normal domain term below `Ω_{b+1}` is accessible, by induction on `b`. -/
theorem accD_of_lt_Omega : ∀ (b : ℕ) {t : ThetaWTerm}, NF t → Dom t → t < Omega b → Acc RelD t := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ihb =>
  intro t ht hD hlt
  obtain ⟨M, hM⟩ := exists_levLT t
  have hbN : b < b + M + 1 := by omega
  have hC : Cls b (b + M + 1) 0 t := ⟨hD, Sk.of_levLT (hM.mono (by omega))⟩
  have h0 : HLow b (b + M + 1) 0 := by
    intro s hs hCs hB
    cases b with
    | zero => exact hB.elim
    | succ c => exact acc_mono (fun _ h => h.1) (ihb c (by omega) hs hCs.1 hB)
  exact accD_of_acc_cls0 hbN t (acc_cls0_of_lt_Omega h0 ht hC hlt) ht hC hlt

/-- **Every normal domain term is accessible**, for all levels. -/
theorem accD {t : ThetaWTerm} (ht : NF t) (hD : Dom t) : Acc RelD t := by
  obtain ⟨n, hn⟩ := exists_levLT t
  exact accD_of_lt_Omega n ht hD (lt_Omega_of_levLT hn)

/-- `≺` on the normal domain terms (as a relation on raw terms) is well founded. -/
theorem wellFounded_relD : WellFounded RelD :=
  ⟨fun a => Acc.intro a fun _ ⟨hb, hD, _⟩ => accD hb hD⟩

end ThetaWTerm

namespace ThetaWNoteD

/-- Every notation is accessible. -/
theorem acc (a : ThetaWNoteD) : Acc (· < ·) a :=
  Subrelation.accessible (q := (· < ·))
    (r := InvImage ThetaWTerm.RelD Subtype.val)
    (fun {x _} h => ⟨x.2.1, x.2.2, h⟩)
    (InvImage.accessible Subtype.val (ThetaWTerm.accD a.2.1 a.2.2))

/-- **The multi-level ϑ-order on the normal domain terms of all levels is well founded.** -/
instance wellFoundedLT : WellFoundedLT ThetaWNoteD := ⟨⟨acc⟩⟩

end ThetaWNoteD

end OrdinalAnalysis
