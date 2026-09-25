/-
  The sharp cofinality of `ϑ₀(ω_m(Ω_{n+1} + 1))` below `c_{n+1} = ϑ₀(ϑ_{n+1} 0)`, and the
  shape of the towers `ω_m(Ω_{n+1} + 1)`.

  `Ordinal/ThetaW/HullCofinal.lean`'s `dom_lt_theta0_omegaTower` bounds a term `a ≺ c_n` by
  `ϑ₀(ω_m(Ω_{n+1} + 1))` (Lean `Omega n` is `Ω_{n+1}`), one level more than `ID_n` reaches.  The
  sharp bound, used by the upper bound of `ID_{n+1}`:

  * `lt_omegaTower_of_lt_theta_succ`: a normal term below `ϑ_{n+1} 0` lies below some
    `ω_m(Ω_{n+1} + 1)` (its principal parts are `≼ Ω_{n+1}`: `ϑ_{n+1} ξ ≺ ϑ_{n+1} 0` is
    impossible, `E_{n+1}(0) = ∅`);
  * `lt_theta0_of_lt_c`: a normal term below `c_{n+1}` lies below some `ϑ₀(ω_m(Ω_{n+1} + 1))`
    (by the clause for `ϑ₀`, since `E_0(ϑ_{n+1} 0) = ∅`), by induction on the length as in
    `HullCofinal.exists_lt_theta0_omegaTower_of_levLT`.

  No level bound or domain condition is needed.
-/
import OrdinalAnalysis.Ordinal.ThetaW.HullCofinal

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Upper

open ThetaWTerm
open ThetaWNoteD (omegaTower)

/-! ### The shape of the towers -/

/-- `Ω_{n+1} + 1 = ⟨Ω_{n+1}, 0⟩`. -/
theorem omega_add_one_val (n : ℕ) :
    (ThetaWNoteD.Omega n + ThetaWNoteD.one).1 = sum [Omega n, sum []] := by
  show ofList (addL [Omega n] [sum []]) = _
  have h : geb (Omega n) (sum []) = true := by
    simp only [geb, decide_eq_true_eq]
    exact Or.inl (nil_lt_Omega n)
  rw [addL_cons, List.filter_singleton, h]
  rfl

/-- The tower is a tower of sums. -/
theorem omegaTower_val (n : ℕ) :
    ∀ m, ∃ xs, (omegaTower m (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1 = sum xs
  | 0 => ⟨_, omega_add_one_val n⟩
  | m + 1 => by
    obtain ⟨xs, hxs⟩ := omegaTower_val n m
    refine ⟨[(omegaTower m (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1], ?_⟩
    show ofList [(omegaTower m (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1] = _
    rw [ofList_singleton_not_prin (by rw [hxs]; exact id)]

/-- `ω_{m+1}(Ω_{n+1} + 1) = ⟨ω_m(Ω_{n+1} + 1)⟩`. -/
theorem omegaTower_succ_val (n m : ℕ) :
    (omegaTower (m + 1) (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1 =
      sum [(omegaTower m (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1] := by
  obtain ⟨xs, hxs⟩ := omegaTower_val n m
  show ofList [(omegaTower m (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1] = _
  rw [ofList_singleton_not_prin (by rw [hxs]; exact id)]

/-! ### The sharp cofinality -/

/-- **A normal term below `ϑ_{n+1} 0` lies below some `ω_m(Ω_{n+1} + 1)`.** -/
theorem lt_omegaTower_of_lt_theta_succ (n : ℕ) : ∀ {t : ThetaWTerm}, NF t →
    t < theta (n + 1) zero →
      ∃ m, t < (omegaTower m (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1
  | Omega j, _, h =>
    ⟨0, by
      have hj : j ≤ n := by have := (Omega_lt_theta_iff j (n + 1) zero).mp h; omega
      show Omega j < (ThetaWNoteD.Omega n + ThetaWNoteD.one).1
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · exact lt_trans ((Omega_lt_Omega_iff j n).mpr hj) (ThetaWNoteD.Omega_lt_Omega_add_one n)
      · exact ThetaWNoteD.Omega_lt_Omega_add_one j⟩
  | theta j a, _, h => by
    have hj : j ≤ n := by
      rcases Nat.lt_trichotomy j (n + 1) with hj | rfl | hj
      · omega
      · exfalso
        rcases (theta_lt_theta_iff (n + 1) a zero).mp h with ⟨h1, _⟩ | ⟨g, hg, _⟩
        · exact not_lt_nil a h1
        · simp [zero] at hg
      · exact absurd h (not_theta_lt_theta_of_lt_level a zero hj)
    refine ⟨0, ?_⟩
    show theta j a < (ThetaWNoteD.Omega n + ThetaWNoteD.one).1
    have h1 : theta j a < Omega j := theta_lt_Omega_self j a
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · exact lt_trans h1 (lt_trans ((Omega_lt_Omega_iff j n).mpr hj)
        (ThetaWNoteD.Omega_lt_Omega_add_one n))
    · exact lt_trans h1 (ThetaWNoteD.Omega_lt_Omega_add_one j)
  | sum [], _, _ =>
    ⟨0, lt_trans (nil_lt_Omega n) (ThetaWNoteD.Omega_lt_Omega_add_one n)⟩
  | sum (x :: xs), hn, h => by
    have hxs : Desc (x :: xs) := hn.desc
    have hSO : SingleOK (x :: xs) := ((nf_sum_iff (x :: xs)).mp hn).2.2
    have hlt : ∀ y ∈ x :: xs, y < theta (n + 1) zero :=
      (sum_lt_prin_iff (isPrin_theta (n + 1) zero) hxs).mp h
    have hbound : ∀ y ∈ x :: xs,
        ∃ m, y < (omegaTower m (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1 := fun y hy =>
      lt_omegaTower_of_lt_theta_succ n (hn.of_mem hy) (hlt y hy)
    obtain ⟨N, hN⟩ := ThetaWNoteD.exists_bound_hull
      (p := fun y m => y < (omegaTower m (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1)
      (fun _ _ _ hmn h => ThetaWTerm.lt_of_lt_of_le' h
        (ThetaWNoteD.le_iff.mp (ThetaWNoteD.omegaTower_le_omegaTower hmn)))
      (x :: xs) hbound
    refine ⟨N + 1, ?_⟩
    have heq1 : sum (x :: xs) = ofList (x :: xs) := (ofList_of_singleOK hSO).symm
    have heq2 : (omegaTower (N + 1) (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1 =
        ofList [(omegaTower N (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1] := rfl
    rw [heq1, heq2, ofList_lt_ofList]
    exact (sum_lt_singleton_iff (desc_iff_pairwise.mp hxs) _).mpr hN
termination_by t => l t
decreasing_by exact l_lt_of_mem hy

/-- **A normal term below `c_{n+1}` lies below some `ϑ₀(ω_m(Ω_{n+1} + 1))`.** -/
theorem lt_theta0_of_lt_c (n : ℕ) : ∀ {t : ThetaWTerm}, NF t → t < cTerm (n + 1) →
    ∃ m, t < theta 0 (omegaTower m (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1
  | Omega j, _, h => absurd ((Omega_lt_theta_iff j 0 _).mp h) (Nat.not_lt_zero j)
  | theta j d, hn, h => by
    have hj0 : j = 0 := by
      rcases Nat.eq_zero_or_pos j with hj | hj
      · exact hj
      · exact absurd h (not_theta_lt_theta_of_lt_level d _ hj)
    subst hj0
    rcases (theta_lt_theta_iff 0 d (theta (n + 1) zero)).mp h with ⟨h1, h2⟩ | ⟨g, hg, _⟩
    · have hnd : NF d := hn.theta_arg
      obtain ⟨m₀, hm₀⟩ := lt_omegaTower_of_lt_theta_succ n hnd h1
      obtain ⟨N, hN⟩ := ThetaWNoteD.exists_bound_hull
        (p := fun g m => g < theta 0 (omegaTower m (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1)
        (fun _ _ _ hmn h => ThetaWTerm.lt_of_lt_of_le' h (ThetaWNoteD.le_iff.mp
          (ThetaWNoteD.theta_omegaTower_le_theta_omegaTower hmn
            (ThetaWNoteD.dom_theta_omegaTower 0 n _) (ThetaWNoteD.dom_theta_omegaTower 0 n _))))
        (E 0 d) fun g hg => lt_theta0_of_lt_c n (NF.of_mem_E hnd hg) (h2 g hg)
      refine ⟨max m₀ N, theta_lt_theta_of_lt ?_ fun g hg => ?_⟩
      · exact lt_of_lt_of_le hm₀
          (ThetaWNoteD.le_iff.mp (ThetaWNoteD.omegaTower_le_omegaTower (le_max_left m₀ N)))
      · exact lt_of_lt_of_le (hN g hg) (ThetaWNoteD.le_iff.mp
          (ThetaWNoteD.theta_omegaTower_le_theta_omegaTower (le_max_right m₀ N)
            (ThetaWNoteD.dom_theta_omegaTower 0 n _) (ThetaWNoteD.dom_theta_omegaTower 0 n _)))
    · rw [E_theta_of_lt (Nat.succ_pos n)] at hg
      simp [zero] at hg
  | sum [], _, _ => ⟨0, nil_lt_theta 0 _⟩
  | sum (x :: xs), hn, h => by
    obtain ⟨m, hm⟩ := lt_theta0_of_lt_c n (hn.of_mem List.mem_cons_self)
      ((cons_lt_theta_iff 0 x (theta (n + 1) zero) xs).mp h)
    exact ⟨m, (cons_lt_theta_iff 0 x _ xs).mpr hm⟩
termination_by t => l t
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · simp; omega

/-- **The sharp cofinality for notations**: `a ≺ c_{n+1}` gives `a ≺ ϑ₀(ω_m(Ω_{n+1} + 1))` for
some `m`. -/
theorem exists_lt_theta0_tower {n : ℕ} {a : ThetaWNoteD} (h : a < ThetaWNoteD.c (n + 1)) :
    ∃ m, a.1 < theta 0 (omegaTower m (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1 :=
  lt_theta0_of_lt_c n a.2.1 h

/-- Every countable notation lies below some `c_{N+1}`. -/
theorem exists_lt_c_succ {a : ThetaWNoteD} (h : a.1 < Omega 0) :
    ∃ N, a < ThetaWNoteD.c (N + 1) := by
  obtain ⟨N, hN⟩ := ThetaWNoteD.exists_lt_theta0Omega a h
  exact ⟨N, lt_trans hN (ThetaWNoteD.theta0Omega_lt_c_succ N)⟩

end OrdinalAnalysis.IDn.Upper
