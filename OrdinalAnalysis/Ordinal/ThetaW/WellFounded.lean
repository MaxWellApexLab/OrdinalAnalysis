/-
  Well-foundedness of the ϑ-order with two levels (`Ω₁`, `Ω₂`, `ϑ₀`, `ϑ₁`).

  Source: T. Arai, *Lectures on ordinal analysis*, arXiv:2304.00246, §1.6 (Definition 1.27,
  Lemma 1.29, Lemma 1.33), the distinguished-class argument for one collapsing function,
  carried out here level by level in the metatheory; the one-level version for Freund's
  ϑ (arXiv:2204.09321, Definition 3.1) is the model.  The order clauses are those of the
  companion module on terms (at one level: Freund's clause (ii') with the level-`k`
  coefficient set `E_k`, cf. G. Wilken, arXiv:2410.15953, Proposition 2.3).

  All terms considered are normal and satisfy `LevLT 2` (only `Ω₁ = Omega 0`, `Ω₂ = Omega 1`,
  `ϑ₀`, `ϑ₁` occur).  The predecessors of such a term inside the whole system may contain
  higher levels (for instance `ϑ₀(ϑ₁(Ω₃)) ≺ ϑ₀(Ω₂)`); the order is therefore restricted to
  the two-level terms, which form a suborder.  The restriction is necessary: on the normal
  terms of all levels the order has the descending sequence
  `ϑ₀(Ω₂) ≻ ϑ₀(ϑ₁(Ω₃)) ≻ ϑ₀(ϑ₁(ϑ₂(Ω₄))) ≻ ⋯` (companion module on descent).

  Write `W₀` for the accessible part of `≺` on the two-level terms, and
    `D₀ = {α | E₀(α) ⊆ W₀}`,       `W₁` = the accessible part of `≺` restricted to `D₀`,
    `D₁ = {α ∈ D₀ | E₁(α) ⊆ W₁}`.
  The argument runs top-down: the collapse of level 1 is handled first, relative to `D₀`,
  and only then the collapse of level 0.

  * (Level 0, Arai Lemma 1.29.)  `D₀ ∩ Ω₁ ⊆ W₀`: a term below `Ω₁` is a sum of `ϑ₀`-terms,
    which are members of `E₀`.  Hence `D₀ ∩ Ω₁ ⊆ W₁` (since `D₀` is contained in the class of
    all two-level terms), and `Ω₁ ∈ W₁`.
  * (Level 1, Arai Lemma 1.29.)  `D₁ ∩ Ω₂ ⊆ W₁`: a term below `Ω₂` is a sum of `Ω₁`,
    `ϑ₀`-terms and `ϑ₁`-terms, the latter two members of `E₁`.
  * (`≺` restricted to `D₁` is well founded.)  Below `Ω₂` by the previous item; `Ω₂` because
    its `D₁`-predecessors lie below `Ω₂`; above `Ω₂` a two-level term is a sum of shorter
    terms of `D₁`, and induction on the length applies.
  * (Level 1, Arai Lemma 1.33.)  If `α ∈ D₁` and `ϑ₁ ξ ∈ W₁` for all `ξ ∈ D₁` with `ξ ≺ α`,
    then `ϑ₁ α ∈ W₁`: for `γ ≺ ϑ₁ α` in `D₀`, by induction on the length of `γ`: `Ω₁` and
    the terms below `Ω₁` are in `W₁`; sums are handled componentwise; for `γ = ϑ₁ ξ` the
    clause leaves the cases `ξ ≺ α ∧ E₁(ξ) ≺* ϑ₁ α`, where `E₀(ξ) = E₀(γ)` and the members of
    `E₁(ξ)` are shorter terms of `D₀` below `ϑ₁ α` (for `δ ∈ E₁(ξ)` one has `E₀(δ) ⊆ E₀(ξ)`),
    so `ξ ∈ D₁`; and `ϑ₁ ξ ≼ δ ∈ E₁(α) ⊆ W₁`.
    By induction along `≺` restricted to `D₁`: `ϑ₁ α ∈ W₁` for all `α ∈ D₁`.
  * (Collapse of the class, `D₀ ⊆ D₁`.)  By induction on the length: a member of `E₁(α)`
    for `α ∈ D₀` is either `ϑ₀ δ ∈ E₀(α) ⊆ W₀ ⊆ W₁` or `ϑ₁ δ` with `δ ∈ D₀` shorter, hence
    `δ ∈ D₁` and `ϑ₁ δ ∈ W₁`.  Consequently `≺` restricted to `D₀` is well founded.
  * (Level 0, Arai Lemma 1.33.)  If `α ∈ D₀` and `ϑ₀ ξ ∈ W₀` for all `ξ ∈ D₀` with `ξ ≺ α`,
    then `ϑ₀ α ∈ W₀` — exactly the one-level argument with `E₀`.  By induction along `≺`
    restricted to `D₀`, `ϑ₀ α ∈ W₀` for all `α ∈ D₀`.
  * Every term below `Ω₁` is in `W₀` (induction on the length), so every two-level term is in
    `D₀`, and `D₀ ⊆ W₀` by the well-foundedness of `≺` restricted to `D₀`.
-/
import OrdinalAnalysis.Ordinal.ThetaW.Exponents

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

/-! ### Coefficients of coefficients -/

/-- For `j ≤ k`, the level-`j` coefficients of a level-`k` coefficient of `α` are level-`j`
coefficients of `α`. -/
theorem mem_E_of_mem_E {j k : ℕ} (hjk : j ≤ k) :
    ∀ {a g h : ThetaWTerm}, g ∈ E k a → h ∈ E j g → h ∈ E j a
  | Omega _, _, _, hg, _ => by simp at hg
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

/-! ### Accessibility, restricted to a class -/

/-- The order `≺` on normal terms, restricted to a class `S`. -/
def RelOn (S : ThetaWTerm → Prop) (a b : ThetaWTerm) : Prop := NF a ∧ S a ∧ a < b

/-- The two-level terms. -/
abbrev L2 : ThetaWTerm → Prop := LevLT 2

/-- `a` lies in the accessible part `W₀` of `≺` on the normal two-level terms. -/
def IsAcc (a : ThetaWTerm) : Prop := Acc (RelOn L2) a

theorem acc_of_le {S : ThetaWTerm → Prop} {a b : ThetaWTerm} (hb : Acc (RelOn S) b)
    (ha : NF a) (hS : S a) (h : a ≤ b) : Acc (RelOn S) a := by
  rcases h with h | rfl
  · exact Acc.inv hb ⟨ha, hS, h⟩
  · exact hb

/-- Accessibility for a larger class gives accessibility for a smaller one. -/
theorem acc_mono {S T : ThetaWTerm → Prop} (hST : ∀ a, S a → T a) {a : ThetaWTerm}
    (h : Acc (RelOn T) a) : Acc (RelOn S) a :=
  Subrelation.accessible (fun ⟨h1, h2, h3⟩ => ⟨h1, hST _ h2, h3⟩) h

/-- `0 = ⟨⟩` has no predecessors. -/
theorem acc_nil (S : ThetaWTerm → Prop) : Acc (RelOn S) (sum []) :=
  Acc.intro _ fun _ h => absurd h.2.2 (not_lt_nil _)

/-! ### Sums of accessible exponents are accessible -/

section Sums

variable (S : ThetaWTerm → Prop) (hS : ∀ xs, S (ofList xs) ↔ ∀ x ∈ xs, S x)
include hS

/-- The inner induction: for a fixed first exponent `x`, assuming the claim for all smaller
first exponents, `ofList (x :: ys)` is accessible whenever `ofList ys` is. -/
theorem acc_ofList_cons_aux {x : ThetaWTerm}
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

/-- The outer induction, on the first exponent. -/
theorem acc_ofList_of_le (x : ThetaWTerm) (hx : Acc (RelOn S) x) :
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
theorem acc_of_toList {t : ThetaWTerm} (ht : NF t) (hSy : ∀ y ∈ toList t, S y)
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

/-! ### The classes `D₀` and `D₁` -/

/-- `D₀`: the two-level terms whose level-0 coefficients are in `W₀`. -/
def D0 (a : ThetaWTerm) : Prop := L2 a ∧ ∀ g ∈ E 0 a, IsAcc g

/-- `a` lies in `W₁`, the accessible part of `≺` restricted to `D₀`. -/
def W1 (a : ThetaWTerm) : Prop := Acc (RelOn D0) a

/-- `D₁`: the terms of `D₀` whose level-1 coefficients are in `W₁`. -/
def D1 (a : ThetaWTerm) : Prop := D0 a ∧ ∀ g ∈ E 1 a, W1 g

theorem l2_ofList_iff (xs : List ThetaWTerm) : L2 (ofList xs) ↔ ∀ x ∈ xs, L2 x :=
  levLT_ofList_iff

theorem d0_ofList_iff (xs : List ThetaWTerm) : D0 (ofList xs) ↔ ∀ x ∈ xs, D0 x := by
  unfold D0
  rw [l2_ofList_iff]
  constructor
  · rintro ⟨h1, h2⟩ x hx
    exact ⟨h1 x hx, fun g hg => h2 g (mem_E_ofList.mpr ⟨x, hx, hg⟩)⟩
  · intro h
    refine ⟨fun x hx => (h x hx).1, fun g hg => ?_⟩
    obtain ⟨x, hx, hg⟩ := mem_E_ofList.mp hg
    exact (h x hx).2 g hg

theorem d1_ofList_iff (xs : List ThetaWTerm) : D1 (ofList xs) ↔ ∀ x ∈ xs, D1 x := by
  unfold D1
  rw [d0_ofList_iff]
  constructor
  · rintro ⟨h1, h2⟩ x hx
    exact ⟨h1 x hx, fun g hg => h2 g (mem_E_ofList.mpr ⟨x, hx, hg⟩)⟩
  · intro h
    refine ⟨fun x hx => (h x hx).1, fun g hg => ?_⟩
    obtain ⟨x, hx, hg⟩ := mem_E_ofList.mp hg
    exact (h x hx).2 g hg

theorem D0.of_mem {x : ThetaWTerm} {xs : List ThetaWTerm} (h : D0 (sum xs)) (hx : x ∈ xs) :
    D0 x :=
  ⟨(levLT_sum_iff 2 xs).mp h.1 x hx, fun g hg => h.2 g (mem_E_of_mem hx hg)⟩

theorem D1.of_mem {x : ThetaWTerm} {xs : List ThetaWTerm} (h : D1 (sum xs)) (hx : x ∈ xs) :
    D1 x :=
  ⟨h.1.of_mem hx, fun g hg => h.2 g (mem_E_of_mem hx hg)⟩

/-- The level-1 coefficients of a term of `D₀` are in `D₀`. -/
theorem D0.of_mem_E1 {a g : ThetaWTerm} (h : D0 a) (hg : g ∈ E 1 a) : D0 g :=
  ⟨LevLT.of_mem_E h.1 hg, fun _ hd => h.2 _ (mem_E_of_mem_E (Nat.zero_le 1) hg hd)⟩

/-- `D₀` passes from `ϑ₁ ξ` to `ξ`, since `E₀(ϑ₁ ξ) = E₀(ξ)`. -/
theorem D0.theta1_arg {ξ : ThetaWTerm} (h : D0 (theta 1 ξ)) : D0 ξ :=
  ⟨((levLT_theta 2 1 ξ).mp h.1).2,
    fun g hg => h.2 g (by rw [E_theta_of_lt Nat.zero_lt_one]; exact hg)⟩

/-- A two-level principal term above `Ω₂` does not exist. -/
theorem not_prin_above_Omega1 {a : ThetaWTerm} (hp : IsPrin a) (hL : L2 a)
    (hk : key (Omega 1) < key a) : False := by
  cases a with
  | sum _ => exact hp
  | Omega j => simp at hL hk; omega
  | theta j b => simp at hL hk; omega

/-! ### Level 0 below `Ω₁` (Arai, Lemma 1.29) -/

/-- `D₀ ∩ Ω₁ ⊆ W₀`. -/
theorem isAcc_of_D0_of_lt_Omega0 : ∀ {a : ThetaWTerm}, NF a → D0 a → a < Omega 0 → IsAcc a
  | Omega j, _, _, h => absurd ((Omega_lt_Omega_iff j 0).mp h) (Nat.not_lt_zero j)
  | theta j ξ, _, hD, h => by
    have := (theta_lt_Omega_iff j 0 ξ).mp h
    exact hD.2 (theta j ξ) (by rw [E_theta_of_le this]; simp)
  | sum xs, ha, hD, hlt => by
    have hxs : ∀ x ∈ xs, x < Omega 0 := (sum_lt_prin_iff (isPrin_Omega 0) ha.desc).mp hlt
    exact acc_of_toList L2 l2_ofList_iff ha (fun x hx => (hD.of_mem hx).1) fun x hx =>
      isAcc_of_D0_of_lt_Omega0 (ha.of_mem hx) (hD.of_mem hx) (hxs x hx)
termination_by a => l a
decreasing_by exact l_lt_of_mem hx

theorem W1_of_isAcc {a : ThetaWTerm} (h : IsAcc a) : W1 a := acc_mono (fun _ h => h.1) h

theorem W1_of_D0_of_lt_Omega0 {a : ThetaWTerm} (ha : NF a) (hD : D0 a) (h : a < Omega 0) :
    W1 a :=
  W1_of_isAcc (isAcc_of_D0_of_lt_Omega0 ha hD h)

/-- `Ω₁ ∈ W₁`. -/
theorem W1_Omega0 : W1 (Omega 0) :=
  Acc.intro _ fun _ ⟨hz, hD, hlt⟩ => W1_of_D0_of_lt_Omega0 hz hD hlt

/-! ### Level 1 below `Ω₂` (Arai, Lemma 1.29) -/

/-- `D₁ ∩ Ω₂ ⊆ W₁`. -/
theorem W1_of_D1_of_lt_Omega1 : ∀ {a : ThetaWTerm}, NF a → D1 a → a < Omega 1 → W1 a
  | Omega j, _, _, h => by
    have := (Omega_lt_Omega_iff j 1).mp h
    obtain rfl : j = 0 := by omega
    exact W1_Omega0
  | theta j ξ, _, hD, h => by
    have := (theta_lt_Omega_iff j 1 ξ).mp h
    exact hD.2 (theta j ξ) (by rw [E_theta_of_le this]; simp)
  | sum xs, ha, hD, hlt => by
    have hxs : ∀ x ∈ xs, x < Omega 1 := (sum_lt_prin_iff (isPrin_Omega 1) ha.desc).mp hlt
    exact acc_of_toList D0 d0_ofList_iff ha (fun x hx => hD.1.of_mem hx) fun x hx =>
      W1_of_D1_of_lt_Omega1 (ha.of_mem hx) (hD.of_mem hx) (hxs x hx)
termination_by a => l a
decreasing_by exact l_lt_of_mem hx

/-! ### The order restricted to `D₁` is well founded -/

theorem acc_D1 : ∀ (n : ℕ) {a : ThetaWTerm}, l a ≤ n → NF a → D1 a → Acc (RelOn D1) a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn ha hD
  rcases lt_trichotomy' a (Omega 1) with h | rfl | h
  · exact acc_mono (fun _ h => h.1) (W1_of_D1_of_lt_Omega1 ha hD h)
  · exact Acc.intro _ fun _ ⟨hz, hDz, hlt⟩ =>
      acc_mono (fun _ h => h.1) (W1_of_D1_of_lt_Omega1 hz hDz hlt)
  · rcases Omega_lt_iff.mp h with ⟨hp, hk⟩ | ⟨c, cs, rfl, _⟩
    · exact (not_prin_above_Omega1 hp hD.1.1 hk).elim
    · refine acc_of_toList D1 d1_ofList_iff ha (fun x hx => hD.of_mem hx) fun x hx => ?_
      have hl := l_lt_of_mem (xs := c :: cs) hx
      exact ih (l x) (by omega) le_rfl (ha.of_mem hx) (hD.of_mem hx)

/-! ### The main lemma at level 1 (Arai, Lemma 1.33, for `ϑ₁`) -/

/-- The induction on the length of `γ ≺ ϑ₁ α` in the main lemma at level 1. -/
theorem W1_of_lt_theta1 {α : ThetaWTerm} (hM : D1 α)
    (hyp : ∀ ξ, NF ξ → D1 ξ → ξ < α → W1 (theta 1 ξ)) :
    ∀ {γ : ThetaWTerm}, NF γ → D0 γ → γ < theta 1 α → W1 γ
  | Omega j, _, _, h => by
    have := (Omega_lt_theta_iff j 1 α).mp h
    obtain rfl : j = 0 := by omega
    exact W1_Omega0
  | theta j ξ, hγ, hD, h => by
    rcases Nat.lt_or_ge j 1 with hj | hj
    · exact W1_of_D0_of_lt_Omega0 hγ hD ((theta_lt_Omega_iff j 0 ξ).mpr (by omega))
    · have hj1 : j = 1 := by
        rcases Nat.lt_or_ge 1 j with h' | h'
        · exact absurd h (not_theta_lt_theta_of_lt_level ξ α h')
        · omega
      subst hj1
      rcases (theta_lt_theta_iff 1 ξ α).mp h with ⟨h1, h2⟩ | ⟨g, hg, h3⟩
      · have hξ : D0 ξ := hD.theta1_arg
        refine hyp ξ hγ.theta_arg ⟨hξ, fun g hg => ?_⟩ h1
        exact W1_of_lt_theta1 hM hyp (NF.of_mem_E hγ.theta_arg hg) (hξ.of_mem_E1 hg) (h2 g hg)
      · exact acc_of_le (hM.2 g hg) hγ hD h3
  | sum xs, hγ, hD, h => by
    have hxs : ∀ x ∈ xs, x < theta 1 α := (sum_lt_prin_iff (isPrin_theta 1 α) hγ.desc).mp h
    exact acc_of_toList D0 d0_ofList_iff hγ (fun x hx => hD.of_mem hx) fun x hx =>
      W1_of_lt_theta1 hM hyp (hγ.of_mem hx) (hD.of_mem hx) (hxs x hx)
termination_by γ => l γ
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · exact l_lt_of_mem hx

/-- `ϑ₁` maps `D₁` into `W₁`, by induction along `≺` restricted to `D₁`. -/
theorem W1_theta1 {α : ThetaWTerm} (hα : NF α) (hM : D1 α) : W1 (theta 1 α) := by
  suffices ∀ a, Acc (RelOn D1) a → NF a → D1 a → W1 (theta 1 a) from
    this α (acc_D1 _ le_rfl hα hM) hα hM
  intro a h
  induction h with
  | intro a _ ih =>
  intro _ hMa
  exact Acc.intro _ fun _ ⟨hγ, hDγ, hlt⟩ =>
    W1_of_lt_theta1 hMa (fun ξ hξ hMξ hlt' => ih ξ ⟨hξ, hMξ, hlt'⟩ hξ hMξ) hγ hDγ hlt

/-! ### Collapse of the class: `D₀ ⊆ D₁` -/

theorem D1_of_D0 : ∀ (n : ℕ) {a : ThetaWTerm}, l a ≤ n → NF a → D0 a → D1 a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn ha hD
  refine ⟨hD, fun g hg => ?_⟩
  have hgD : D0 g := hD.of_mem_E1 hg
  have hgN : NF g := NF.of_mem_E ha hg
  have hgl := l_le_of_mem_E hg
  obtain ⟨j, d, hj, rfl⟩ := exists_eq_theta_of_mem_E hg
  rcases Nat.lt_or_ge j 1 with hj0 | hj1
  · exact W1_of_D0_of_lt_Omega0 hgN hgD ((theta_lt_Omega_iff j 0 d).mpr (by omega))
  · obtain rfl : j = 1 := by omega
    simp only [l_theta] at hgl
    exact W1_theta1 hgN.theta_arg
      (ih (l d) (by omega) le_rfl hgN.theta_arg hgD.theta1_arg)

theorem D1_of_D0' {a : ThetaWTerm} (ha : NF a) (hD : D0 a) : D1 a := D1_of_D0 _ le_rfl ha hD

/-- The order restricted to `D₀` is well founded on `D₀`. -/
theorem acc_D0 {a : ThetaWTerm} (ha : NF a) (hD : D0 a) : Acc (RelOn D0) a := by
  suffices ∀ a, Acc (RelOn D1) a → Acc (RelOn D0) a from
    this a (acc_D1 _ le_rfl ha (D1_of_D0' ha hD))
  intro a h
  induction h with
  | intro a _ ih =>
  exact Acc.intro _ fun z ⟨hz, hDz, hlt⟩ => ih z ⟨hz, D1_of_D0' hz hDz, hlt⟩

/-! ### The main lemma at level 0 (Arai, Lemma 1.33, for `ϑ₀`) -/

/-- The induction on the length of `γ ≺ ϑ₀ α` in the main lemma at level 0. -/
theorem isAcc_of_lt_theta0 {α : ThetaWTerm} (hM : D0 α)
    (hyp : ∀ ξ, NF ξ → D0 ξ → ξ < α → IsAcc (theta 0 ξ)) :
    ∀ {γ : ThetaWTerm}, NF γ → L2 γ → γ < theta 0 α → IsAcc γ
  | Omega j, _, _, h => absurd ((Omega_lt_theta_iff j 0 α).mp h) (Nat.not_lt_zero j)
  | theta j ξ, hγ, hL, h => by
    have hj : j = 0 := by
      rcases Nat.eq_zero_or_pos j with h' | h'
      · exact h'
      · exact absurd h (not_theta_lt_theta_of_lt_level ξ α h')
    subst hj
    have hLξ : L2 ξ := ((levLT_theta 2 0 ξ).mp hL).2
    rcases (theta_lt_theta_iff 0 ξ α).mp h with ⟨h1, h2⟩ | ⟨g, hg, h3⟩
    · exact hyp ξ hγ.theta_arg ⟨hLξ, fun g hg => isAcc_of_lt_theta0 hM hyp
        (NF.of_mem_E hγ.theta_arg hg) (LevLT.of_mem_E hLξ hg) (h2 g hg)⟩ h1
    · exact acc_of_le (hM.2 g hg) hγ hL h3
  | sum xs, hγ, hL, h => by
    have hxs : ∀ x ∈ xs, x < theta 0 α := (sum_lt_prin_iff (isPrin_theta 0 α) hγ.desc).mp h
    have hLx : ∀ x ∈ xs, L2 x := (levLT_sum_iff 2 xs).mp hL
    exact acc_of_toList L2 l2_ofList_iff hγ hLx fun x hx =>
      isAcc_of_lt_theta0 hM hyp (hγ.of_mem hx) (hLx x hx) (hxs x hx)
termination_by γ => l γ
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · exact l_lt_of_mem hx

/-- `ϑ₀` maps `D₀` into `W₀`, by induction along `≺` restricted to `D₀`. -/
theorem isAcc_theta0 {α : ThetaWTerm} (hα : NF α) (hM : D0 α) : IsAcc (theta 0 α) := by
  suffices ∀ a, Acc (RelOn D0) a → NF a → D0 a → IsAcc (theta 0 a) from
    this α (acc_D0 hα hM) hα hM
  intro a h
  induction h with
  | intro a _ ih =>
  intro _ hMa
  exact Acc.intro _ fun _ ⟨hγ, hLγ, hlt⟩ =>
    isAcc_of_lt_theta0 hMa (fun ξ hξ hMξ hlt' => ih ξ ⟨hξ, hMξ, hlt'⟩ hξ hMξ) hγ hLγ hlt

/-! ### Every two-level normal term is accessible -/

/-- Every two-level normal term below `Ω₁` is accessible. -/
theorem isAcc_of_lt_Omega0 : ∀ {a : ThetaWTerm}, NF a → L2 a → a < Omega 0 → IsAcc a
  | Omega j, _, _, h => absurd ((Omega_lt_Omega_iff j 0).mp h) (Nat.not_lt_zero j)
  | theta j ξ, ha, hL, h => by
    have hj : j = 0 := Nat.le_zero.mp ((theta_lt_Omega_iff j 0 ξ).mp h)
    subst hj
    have hLξ : L2 ξ := ((levLT_theta 2 0 ξ).mp hL).2
    exact isAcc_theta0 ha.theta_arg ⟨hLξ, fun g hg =>
      isAcc_of_lt_Omega0 (NF.of_mem_E ha.theta_arg hg) (LevLT.of_mem_E hLξ hg)
        (lt_Omega_of_mem_E hg)⟩
  | sum xs, ha, hL, h => by
    have hxs : ∀ x ∈ xs, x < Omega 0 := (sum_lt_prin_iff (isPrin_Omega 0) ha.desc).mp h
    have hLx : ∀ x ∈ xs, L2 x := (levLT_sum_iff 2 xs).mp hL
    exact acc_of_toList L2 l2_ofList_iff ha hLx fun x hx =>
      isAcc_of_lt_Omega0 (ha.of_mem hx) (hLx x hx) (hxs x hx)
termination_by a => l a
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · exact l_lt_of_mem hx

/-- Every two-level normal term lies in `D₀`. -/
theorem d0_of_nf {a : ThetaWTerm} (ha : NF a) (hL : L2 a) : D0 a :=
  ⟨hL, fun _ hg => isAcc_of_lt_Omega0 (NF.of_mem_E ha hg) (LevLT.of_mem_E hL hg)
    (lt_Omega_of_mem_E hg)⟩

/-- Every two-level normal term is accessible. -/
theorem isAcc {a : ThetaWTerm} (ha : NF a) (hL : L2 a) : IsAcc a := by
  suffices ∀ a, Acc (RelOn D0) a → IsAcc a from this a (acc_D0 ha (d0_of_nf ha hL))
  intro a h
  induction h with
  | intro a _ ih =>
  exact Acc.intro _ fun z ⟨hz, hLz, hlt⟩ => ih z ⟨hz, d0_of_nf hz hLz, hlt⟩

/-- The order `≺` on the two-level normal terms is well founded (on raw terms, with the
predecessors taken among the two-level normal terms). -/
theorem wellFounded_relOn_L2 : WellFounded (RelOn L2) :=
  ⟨fun a => Acc.intro a fun _ ⟨hb, hL, _⟩ => isAcc hb hL⟩

end ThetaWTerm

/-- The two-level ϑ-notation: normal terms built from `Ω₁`, `Ω₂`, `ϑ₀` and `ϑ₁`. -/
def ThetaW2Note : Type := {t : ThetaWTerm // ThetaWTerm.NF t ∧ ThetaWTerm.LevLT 2 t}

instance : DecidableEq ThetaW2Note :=
  inferInstanceAs (DecidableEq {t : ThetaWTerm // ThetaWTerm.NF t ∧ ThetaWTerm.LevLT 2 t})

instance ThetaW2Note.linearOrder : LinearOrder ThetaW2Note :=
  inferInstanceAs (LinearOrder {t : ThetaWTerm // ThetaWTerm.NF t ∧ ThetaWTerm.LevLT 2 t})

namespace ThetaW2Note

theorem lt_iff {a b : ThetaW2Note} : a < b ↔ a.1 < b.1 := Iff.rfl

/-- Every two-level notation is accessible. -/
theorem acc (a : ThetaW2Note) : Acc (· < ·) a :=
  Subrelation.accessible (q := (· < ·))
    (r := InvImage (ThetaWTerm.RelOn ThetaWTerm.L2) Subtype.val)
    (fun {x _} h => ⟨x.2.1, x.2.2, h⟩)
    (InvImage.accessible Subtype.val (ThetaWTerm.isAcc a.2.1 a.2.2))

/-- **The two-level ϑ-order on normal terms is well founded.** -/
instance wellFoundedLT : WellFoundedLT ThetaW2Note := ⟨⟨acc⟩⟩

end ThetaW2Note

end OrdinalAnalysis
