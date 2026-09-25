/-
  The cofinality lemmas for the countable part of the multi-level ϑ-notation, level `0`.

  Source: A. Freund, arXiv:2204.09321, Definition 3.1 (ii') and §5 (`ω(α)`); ported from
  `Ordinal/Theta/HullCofinal.lean` (which see for the un-generalized one-level argument this
  file follows), together with `ThetaW/Dom.lean`'s `c n = ϑ₀(ϑ_n 0)`, `dom_cTerm`,
  `lt_theta0_Omega_of_levLT`, `exists_levLT`, `exists_lt_theta0Omega`, and
  `ThetaW/WellFoundedD.lean`'s `levLT_of_lt_of_lt_Omega0` (predecessors of a countable
  `LevLT N` domain term stay `LevLT N`).

  Write `ω₀(α) = α`, `ω_{m+1}(α) = ω(ω_m(α))` (`omegaTower`, exactly as in the one-level file).
  Two cofinality facts are proved, both for the countable (level-`0`) part of the notation:

  * `exists_lt_theta0_omegaTower_of_levLT`: every domain-free normal term with levels `< n + 1`
    that lies below `Ω₁` lies below `ϑ₀(ω_m(Ω_n + 1))` for some `m` — the direct multi-level
    generalization of the one-level file's `exists_lt_theta_omegaTower`, with `Ω` replaced by
    `Ω_n` (fixed) and an explicit level bound `n + 1` added.  The level bound is *necessary*,
    not an artefact: `Ω_{n+1}` itself is never below any `ϑ₀(ω_m(Ω_n + 1))`, since
    `ω_m(Ω_n + 1) < Ω_{n+1}` for every `m` (`omegaTower_lt_Omega_succ`).
  * `dom_lt_theta0_omegaTower` (**the first headline result**, `a ≺ c_n ⇒ a ≺ ϑ₀(ω_m(Ω_n+1))`):
    a domain term `a ≺ c_n` automatically has `LevLT (n + 1) a`
    (`ThetaW/WellFoundedD.levLT_of_lt_of_lt_Omega0`, applied at `t := c_n` itself, which has
    `LevLT (n + 1) c_n` since its only collapse levels are `0` and `n`), so the level bound of
    the first fact is not an extra hypothesis here — it is *derived* from `a ≺ c_n`, using
    machinery already built for `WellFoundedD`, not new machinery.
  * `dom_exists_lt_c` (**the second headline result**, `a ≺ Ω₁ ⇒ ∃ n, a ≺ c_n`): every countable
    domain term lies below some `c_n`, via the *already proved* `ThetaWNoteD.exists_lt_theta0Omega`
    (`a ≺ Ω₁ ⇒ ∃ N, a ≺ ϑ₀(Ω_N)`) together with `theta0Omega_lt_c_succ`
    (`ϑ₀(Ω_N) ≺ c_{N+1}`, since `Ω_N ≺ ϑ_{N+1}(0)` by `Omega_lt_theta_succ`).
-/
import OrdinalAnalysis.Ordinal.ThetaW.Hull
import OrdinalAnalysis.Ordinal.ThetaW.WellFoundedD

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWNoteD

open ThetaWTerm

/-! ### The tower `ω_m(α)` -/

/-- The tower `ω₀(α) = α`, `ω_{m+1}(α) = ω(ω_m(α))`. -/
def omegaTower : ℕ → ThetaWNoteD → ThetaWNoteD
  | 0, x => x
  | m + 1, x => omegaPow (omegaTower m x)

@[simp] theorem omegaTower_zero (x : ThetaWNoteD) : omegaTower 0 x = x := rfl

@[simp] theorem omegaTower_succ (m : ℕ) (x : ThetaWNoteD) :
    omegaTower (m + 1) x = omegaPow (omegaTower m x) := rfl

theorem Omega_lt_Omega_add_one (k : ℕ) : Omega k < Omega k + one := by
  have h := add_lt_add_left (Omega k) zero_lt_one
  rwa [add_zero] at h

/-! ### `E_k` vanishes on `ω_m(Ω_n + 1)`, every level `k` -/

/-- `Ehull k a = ∅ ↔ E_k(α) = []` (the raw and the set-of-notations form agree). -/
theorem Ehull_eq_nil_iff {k : ℕ} {a : ThetaWNoteD} : Ehull k a = ∅ ↔ E k a.1 = [] := by
  constructor
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro g hg
    have hgn : NF g := a.2.1.of_mem_E hg
    have hgd : Dom g := a.2.2.of_mem_E hg
    have hmem : (⟨g, hgn, hgd⟩ : ThetaWNoteD) ∈ Ehull k a := hg
    rw [h] at hmem
    exact hmem
  · intro h
    ext g
    simp [mem_Ehull, h]

/-- `E_k(Ω_n + 1) = ∅`, every level `k`. -/
theorem Ehull_Omega_add_one_hull (k n : ℕ) : Ehull k (Omega n + one) = ∅ :=
  Set.eq_empty_of_subset_empty
    ((Ehull_add_subset_hull k (Omega n) one).trans (by simp))

/-- `E_k(ω_m(Ω_n + 1)) = ∅`, every level `k`. -/
theorem Ehull_omegaTower_hull (k n m : ℕ) : Ehull k (omegaTower m (Omega n + one)) = ∅ := by
  induction m with
  | zero => rw [omegaTower_zero]; exact Ehull_Omega_add_one_hull k n
  | succ m ih => rw [omegaTower_succ, Ehull_omegaPow_hull, ih]

theorem E_omegaTower_hull (k n m : ℕ) : E k (omegaTower m (Omega n + one)).1 = [] :=
  Ehull_eq_nil_iff.mp (Ehull_omegaTower_hull k n m)

/-! ### `ω_m(Ω_n + 1)` is strictly increasing in `m` -/

theorem omegaTower_lt_omegaTower_succ (n m : ℕ) :
    omegaTower m (Omega n + one) < omegaTower (m + 1) (Omega n + one) := by
  induction m with
  | zero =>
    rw [omegaTower_succ, omegaTower_zero, lt_omegaPow_iff, entries_add]
    intro e he
    rcases mem_addL he with he | he
    · rw [entries_Omega, List.mem_singleton] at he
      rw [he]; exact Omega_lt_Omega_add_one n
    · rw [entries_one, List.mem_singleton] at he
      rw [he]
      have h1 : (zero : ThetaWNoteD) < Omega n := by
        rw [lt_iff]; exact ThetaWTerm.nil_lt_Omega n
      exact lt_trans h1 (Omega_lt_Omega_add_one n)
  | succ m ih => exact omegaPow_lt_omegaPow ih

theorem omegaTower_lt_omegaTower {n m₁ m₂ : ℕ} (h : m₁ < m₂) :
    omegaTower m₁ (Omega n + one) < omegaTower m₂ (Omega n + one) := by
  induction h with
  | refl => exact omegaTower_lt_omegaTower_succ n m₁
  | step _ ih => exact lt_trans ih (omegaTower_lt_omegaTower_succ n _)

theorem omegaTower_le_omegaTower {n m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    omegaTower m₁ (Omega n + one) ≤ omegaTower m₂ (Omega n + one) := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (omegaTower_lt_omegaTower h)
  · exact le_rfl

/-- `ω_m(Ω_n + 1) ≺ Ω_{n+1}` for every `m`: the towers built on `Ω_n` never reach the next
level.  This is exactly why `exists_lt_theta0_omegaTower_of_levLT` below needs a level bound:
`Ω_{n+1}` itself is never below any `ω_m(Ω_n + 1)`. -/
theorem omegaTower_lt_Omega_succ (n m : ℕ) : omegaTower m (Omega n + one) < Omega (n + 1) := by
  induction m with
  | zero =>
    rw [omegaTower_zero]
    refine add_lt_Omega ?_ ?_
    · exact (Omega_lt_Omega_iff n (n + 1)).mpr (by omega)
    · exact one_lt_prin trivial
  | succ m ih => rw [omegaTower_succ]; exact omegaPow_lt_Omega ih

/-- `ϑ₀(ω_{m₁}(Ω_n + 1)) ≺ ϑ₀(ω_{m₂}(Ω_n + 1))` for `m₁ < m₂` (clause (ii') and
`E_0(ω_{m₁}(Ω_n + 1)) = ∅`). -/
theorem theta_omegaTower_lt_theta_omegaTower {n m₁ m₂ : ℕ} (h : m₁ < m₂)
    (hdom₁ : Dom (ThetaWTerm.theta 0 (omegaTower m₁ (Omega n + one)).1))
    (hdom₂ : Dom (ThetaWTerm.theta 0 (omegaTower m₂ (Omega n + one)).1)) :
    thetaD 0 (omegaTower m₁ (Omega n + one)) hdom₁ <
      thetaD 0 (omegaTower m₂ (Omega n + one)) hdom₂ := by
  show ThetaWTerm.theta 0 _ < ThetaWTerm.theta 0 _
  refine ThetaWTerm.theta_lt_theta_of_lt (omegaTower_lt_omegaTower h) ?_
  rw [E_omegaTower_hull]
  simp

theorem theta_omegaTower_le_theta_omegaTower {n m₁ m₂ : ℕ} (h : m₁ ≤ m₂)
    (hdom₁ : Dom (ThetaWTerm.theta 0 (omegaTower m₁ (Omega n + one)).1))
    (hdom₂ : Dom (ThetaWTerm.theta 0 (omegaTower m₂ (Omega n + one)).1)) :
    thetaD 0 (omegaTower m₁ (Omega n + one)) hdom₁ ≤
      thetaD 0 (omegaTower m₂ (Omega n + one)) hdom₂ := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact le_of_lt (theta_omegaTower_lt_theta_omegaTower h hdom₁ hdom₂)
  · subst h; exact le_of_eq (by congr 1)

/-! ### `G_k` vanishes on `ω_m(Ω_n + 1)`, every level `k`: it has no `ϑ`-subterm at all -/

/-- If `G_k` vanishes on every entry of a list, it vanishes on `ofList` of the list (this is
`ThetaW/Veblen`'s `G_sum_eq_nil_of_forall`, but through `ofList` via `mem_G_ofList` rather than
through `sum` via `mem_G_sum`). -/
theorem G_ofList_eq_nil {k : ℕ} {xs : List ThetaWTerm} (h : ∀ x ∈ xs, ThetaWTerm.G k x = []) :
    ThetaWTerm.G k (ThetaWTerm.ofList xs) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro g hg
  obtain ⟨x, hx, hgx⟩ := ThetaWTerm.mem_G_ofList.mp hg
  rw [h x hx] at hgx
  exact List.not_mem_nil hgx

/-- `G_k` vanishes on `α + β` whenever it vanishes on the normal domain terms `α`, `β`
(no `<Ω_k` bound needed: `G_k` only ever sees `ϑ_j`-subterms with `j > k`, and `+` introduces
none). -/
theorem G_add_eq_nil_of {k : ℕ} {a b : ThetaWNoteD} (ha : ThetaWTerm.G k a.1 = [])
    (hb : ThetaWTerm.G k b.1 = []) : ThetaWTerm.G k (a + b).1 = [] := by
  have heq : (a + b).1 = ThetaWTerm.ofList (addL a.entries b.entries) := rfl
  rw [heq]
  apply G_ofList_eq_nil
  intro x hx
  rcases mem_addL hx with hx' | hx'
  · exact ThetaWTerm.G_eq_nil_of_mem_toList a.2.1 ha hx'
  · exact ThetaWTerm.G_eq_nil_of_mem_toList b.2.1 hb hx'

/-- `G_k` vanishes on `ω^α` whenever it vanishes on `α`. -/
theorem G_omegaPow_eq_nil_of {k : ℕ} {a : ThetaWNoteD} (ha : ThetaWTerm.G k a.1 = []) :
    ThetaWTerm.G k (omegaPow a).1 = [] := by
  have heq : (omegaPow a).1 = ThetaWTerm.ofList [a.1] := rfl
  rw [heq]
  apply G_ofList_eq_nil
  intro x hx
  rw [List.mem_singleton] at hx
  rw [hx]; exact ha

theorem G_one_eq_nil (k : ℕ) : ThetaWTerm.G k (one : ThetaWNoteD).1 = [] := by
  have heq : (one : ThetaWNoteD).1 = ThetaWTerm.ofList [ThetaWTerm.zero] := rfl
  rw [heq]
  apply G_ofList_eq_nil
  intro x hx
  rw [List.mem_singleton] at hx
  rw [hx, ThetaWTerm.zero]
  exact ThetaWTerm.G_nil k

/-- `ω_m(Ω_n + 1)` has no `ϑ`-subterm at all, so `G_k` vanishes on it for every level `k`
(not just `k = n`: unlike `ThetaW/Veblen.G_eq_nil_of_lt_Omega`, no bound `≺ Ω_k` is used or
needed here). -/
theorem G_omegaTower_eq_nil (k n : ℕ) : ∀ m, ThetaWTerm.G k (omegaTower m (Omega n + one)).1 = []
  | 0 => G_add_eq_nil_of (ThetaWTerm.G_Omega k n) (G_one_eq_nil k)
  | m + 1 => by rw [omegaTower_succ]; exact G_omegaPow_eq_nil_of (G_omegaTower_eq_nil k n m)

/-- `ω_m(Ω_n + 1)` is domain-safe for every `m` and every level `k` (in particular `k = 0`,
which is all that is used below). -/
theorem dom_theta_omegaTower (k n m : ℕ) :
    Dom (ThetaWTerm.theta k (omegaTower m (Omega n + one)).1) :=
  ThetaWTerm.dom_theta_of_G_nil (omegaTower m (Omega n + one)).2.2 (G_omegaTower_eq_nil k n m)

/-! ### The cofinality of `ω_m(Ω_n + 1)` below `Ω_{n+1}`, for `LevLT (n+1)` terms -/

/-- A common bound for finitely many terms, for a property monotone in the bound
(`Ordinal/Theta/HullCofinal.lean`'s `exists_bound_hull`, level-independent). -/
theorem exists_bound_hull {p : ThetaWTerm → ℕ → Prop} (hp : ∀ t m₁ m₂, m₁ ≤ m₂ → p t m₁ → p t m₂) :
    ∀ (xs : List ThetaWTerm), (∀ x ∈ xs, ∃ m, p x m) → ∃ N, ∀ x ∈ xs, p x N
  | [], _ => ⟨0, by simp⟩
  | y :: ys, h => by
    obtain ⟨m, hm⟩ := h y List.mem_cons_self
    obtain ⟨N, hN⟩ := exists_bound_hull hp ys fun x hx => h x (List.mem_cons_of_mem y hx)
    refine ⟨max m N, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp x m _ (le_max_left m N) hm
    · exact hp x N _ (le_max_right m N) (hN x hx)

/-- Every normal term with levels `< n + 1` lies below `ω_m(Ω_n + 1)` for some `m`.  The level
bound is necessary, not an artefact of the proof: `omegaTower_lt_Omega_succ` shows `Ω_{n+1}`
itself is never below any `ω_m(Ω_n + 1)`. -/
theorem exists_lt_omegaTower_of_levLT (n : ℕ) : ∀ {t : ThetaWTerm}, NF t → LevLT (n + 1) t →
    ∃ m, t < (omegaTower m (Omega n + one)).1
  | ThetaWTerm.Omega j, _, hL =>
    ⟨0, by
      have hj : j ≤ n := by have := (levLT_Omega (n + 1) j).mp hL; omega
      show ThetaWTerm.Omega j < (Omega n + one).1
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · exact lt_trans ((Omega_lt_Omega_iff j n).mpr hj) (Omega_lt_Omega_add_one n)
      · exact Omega_lt_Omega_add_one j⟩
  | ThetaWTerm.theta j a, _, hL =>
    ⟨0, by
      have hj : j ≤ n := by have := (levLT_theta (n + 1) j a).mp hL; omega
      show ThetaWTerm.theta j a < (Omega n + one).1
      have h1 : ThetaWTerm.theta j a < ThetaWTerm.Omega j := ThetaWTerm.theta_lt_Omega_self j a
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · exact lt_trans h1 (lt_trans ((Omega_lt_Omega_iff j n).mpr hj) (Omega_lt_Omega_add_one n))
      · exact lt_trans h1 (Omega_lt_Omega_add_one j)⟩
  | ThetaWTerm.sum [], _, _ => ⟨0, lt_trans (ThetaWTerm.nil_lt_Omega n) (Omega_lt_Omega_add_one n)⟩
  | ThetaWTerm.sum (x :: xs), hn, hL => by
      have hxs : Desc (x :: xs) := hn.desc
      have hSO : SingleOK (x :: xs) := ((nf_sum_iff (x :: xs)).mp hn).2.2
      have hbound : ∀ y ∈ x :: xs, ∃ m, y < (omegaTower m (Omega n + one)).1 := fun y hy =>
        exists_lt_omegaTower_of_levLT n (hn.of_mem hy)
          ((levLT_sum_iff (n + 1) (x :: xs)).mp hL y hy)
      obtain ⟨N, hN⟩ := exists_bound_hull
        (p := fun y m => y < (omegaTower m (Omega n + one)).1)
        (fun _ _ _ hmn h =>
          ThetaWTerm.lt_of_lt_of_le' h (ThetaWNoteD.le_iff.mp (omegaTower_le_omegaTower hmn)))
        (x :: xs) hbound
      refine ⟨N + 1, ?_⟩
      have heq1 : ThetaWTerm.sum (x :: xs) = ThetaWTerm.ofList (x :: xs) :=
        (ofList_of_singleOK hSO).symm
      have heq2 : (omegaTower (N + 1) (Omega n + one)).1 =
          ThetaWTerm.ofList [(omegaTower N (Omega n + one)).1] := rfl
      rw [heq1, heq2, ofList_lt_ofList]
      exact (sum_lt_singleton_iff (ThetaWTerm.desc_iff_pairwise.mp hxs) _).mpr hN
termination_by t => l t
decreasing_by exact l_lt_of_mem hy

/-- **The first headline cofinality fact**: every normal term with levels `< n + 1` that lies
below `Ω₁` lies below `ϑ₀(ω_m(Ω_n + 1))` for some `m` (the direct multi-level generalization of
`Ordinal/Theta/HullCofinal.lean`'s `exists_lt_theta_omegaTower`, by the same induction on the
length: it recurses through `E_0`, using `exists_lt_omegaTower_of_levLT` for the argument of a
`ϑ_0`-collapse and itself, one level down in length, for the (necessarily level-`0`)
coefficients). -/
theorem exists_lt_theta0_omegaTower_of_levLT (n : ℕ) : ∀ {t : ThetaWTerm}, NF t →
    LevLT (n + 1) t → t < ThetaWTerm.Omega 0 →
    ∃ m, t < ThetaWTerm.theta 0 (omegaTower m (Omega n + one)).1
  | ThetaWTerm.Omega j, _, hL, h => absurd ((Omega_lt_Omega_iff j 0).mp h) (Nat.not_lt_zero j)
  | ThetaWTerm.theta j d', hn, hL, h => by
      have hj0 : j = 0 := Nat.le_zero.mp ((theta_lt_Omega_iff j 0 d').mp h)
      subst hj0
      have hLd' : LevLT (n + 1) d' := ((levLT_theta (n + 1) 0 d').mp hL).2
      have hnd' : NF d' := hn.theta_arg
      obtain ⟨m₀, hm₀⟩ := exists_lt_omegaTower_of_levLT n hnd' hLd'
      obtain ⟨N, hN⟩ := exists_bound_hull
        (p := fun g m => g < ThetaWTerm.theta 0 (omegaTower m (Omega n + one)).1)
        (fun _ _ _ hmn h => ThetaWTerm.lt_of_lt_of_le' h (ThetaWNoteD.le_iff.mp
          (theta_omegaTower_le_theta_omegaTower hmn (dom_theta_omegaTower 0 n _)
            (dom_theta_omegaTower 0 n _))))
        (E 0 d')
        fun g hg => exists_lt_theta0_omegaTower_of_levLT n (NF.of_mem_E hnd' hg)
          (LevLT.of_mem_E hLd' hg) (lt_Omega_of_mem_E hg)
      refine ⟨max m₀ N, ThetaWTerm.theta_lt_theta_of_lt ?_ fun g hg => ?_⟩
      · exact lt_of_lt_of_le hm₀
          (ThetaWNoteD.le_iff.mp (omegaTower_le_omegaTower (le_max_left m₀ N)))
      · exact lt_of_lt_of_le (hN g hg) (ThetaWNoteD.le_iff.mp
          (theta_omegaTower_le_theta_omegaTower (le_max_right m₀ N) (dom_theta_omegaTower 0 n _)
            (dom_theta_omegaTower 0 n _)))
  | ThetaWTerm.sum [], _, _, _ => ⟨0, ThetaWTerm.nil_lt_theta 0 _⟩
  | ThetaWTerm.sum (x :: xs), hn, hL, h => by
      obtain ⟨m, hm⟩ := exists_lt_theta0_omegaTower_of_levLT n (hn.of_mem List.mem_cons_self)
        ((levLT_sum_iff (n + 1) (x :: xs)).mp hL x List.mem_cons_self)
        ((cons_lt_Omega_iff 0 x xs).mp h)
      exact ⟨m, (cons_lt_theta_iff 0 x (omegaTower m (Omega n + one)).1 xs).mpr hm⟩
termination_by t => l t
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · simp; omega

/-! ### The two headline cofinality facts -/

theorem levLT_cTerm (n : ℕ) : LevLT (n + 1) (ThetaWTerm.cTerm n) := by
  simp [ThetaWTerm.cTerm, ThetaWTerm.zero, ThetaWTerm.levLT_sum_iff]

/-- **The first headline** (`a ≺ c_n ⇒ a ≺ ϑ₀(ω_m(Ω_n + 1))` for some `m`): a domain term
below `c_n` automatically has `LevLT (n + 1)` (`WellFoundedD.levLT_of_lt_of_lt_Omega0`, applied
at `t := c_n` itself, whose only collapse levels are `0` and `n`), so
`exists_lt_theta0_omegaTower_of_levLT` applies directly — no separate machinery for "predecessors
of `c_n` are level-bounded" was needed beyond what `WellFoundedD` already proved. -/
theorem dom_lt_theta0_omegaTower {n : ℕ} {a : ThetaWNoteD} (h : a < c n) :
    ∃ m, a < thetaD 0 (omegaTower m (Omega n + one)) (dom_theta_omegaTower 0 n m) := by
  have ht : (c n).1 < ThetaWTerm.Omega 0 := ThetaWTerm.cTerm_lt_Omega0 n
  have hL : LevLT (n + 1) a.1 :=
    ThetaWTerm.levLT_of_lt_of_lt_Omega0 (Nat.succ_pos n) a.2.1 a.2.2 (levLT_cTerm n) ht h
  obtain ⟨m, hm⟩ := exists_lt_theta0_omegaTower_of_levLT n a.2.1 hL (lt_trans h ht)
  exact ⟨m, hm⟩

/-- `ϑ₀(Ω_n) ≺ c_{n+1}` (`Ω_n ≺ ϑ_{n+1}(0)` by `Omega_lt_theta_succ`, and `E_0(Ω_n) = ∅`). -/
theorem theta0Omega_lt_c_succ (n : ℕ) : theta0Omega n < c (n + 1) := by
  show ThetaWTerm.theta 0 (ThetaWTerm.Omega n) <
      ThetaWTerm.theta 0 (ThetaWTerm.theta (n + 1) ThetaWTerm.zero)
  refine ThetaWTerm.theta_lt_theta_of_lt (ThetaWTerm.Omega_lt_theta_succ n ThetaWTerm.zero) ?_
  simp

/-- **The second headline** (`a ≺ Ω₁ ⇒ ∃ n, a ≺ c_n`): every countable domain term lies below
some `c_n`, via the already-proved `exists_lt_theta0Omega` (`a ≺ Ω₁ ⇒ ∃ N, a ≺ ϑ₀(Ω_N)`)
shifted one step to a `c`-index by `theta0Omega_lt_c_succ`. -/
theorem dom_exists_lt_c {a : ThetaWNoteD} (h : a.1 < ThetaWTerm.Omega 0) : ∃ n, a < c n := by
  obtain ⟨N, hN⟩ := exists_lt_theta0Omega a h
  exact ⟨N + 1, lt_trans hN (theta0Omega_lt_c_succ N)⟩

end ThetaWNoteD

end OrdinalAnalysis
