/-
  The cofinality of `ϑ₀(ω_m(Ω_ω + 1))` below `Ω₁`, and the shape of the towers `ω_m(Ω_ω + 1)`.

  Replaces `IDn/UpperAuxCof.lean`.  There the bound was per level: a term below
  `c_{n+1} = ϑ₀(ϑ_{n+1} 0)` lies below some `ϑ₀(ω_m(Ω_{n+1} + 1))`, and the argument needed
  `ω_m(Ω_{n+1} + 1)` to dominate every term of level `≤ n + 1`
  (`exists_lt_theta0_omegaTower_of_levLT` with an explicit level bound).  In `ID_ω` the top
  principal term `Ω_ω` bounds every level, so no level bound is needed at all:

  * `lt_omegaTower`: *every* normal term lies below some `ω_m(Ω_ω + 1)` (the principal parts of
    a term are `Ω_j`, `ϑ_j a` or `Ω_ω`, all `≼ Ω_ω`; sums by the length induction of
    `HullCofinal.exists_lt_omegaTower_of_levLT`);
  * `lt_theta0_tower`: a normal term below `Ω₁` lies below some `ϑ₀(ω_m(Ω_ω + 1))`, by induction
    on the length as in `HullCofinal.exists_lt_theta0_omegaTower_of_levLT`.  `ϑ₀(ω_m(Ω_ω+1))` is
    monotone in `m` at the level of terms (`E_0(ω_m(Ω_ω+1)) = ∅`), so neither `Dom` nor the
    hull lemmas of the `ThetaW` side are needed;
  * `exists_lt_tower`: the notation form, the one fact the upper bound of `ID_ω` uses
    (`ThetaVNoteD` has no `Hull/HullCofinal/TowerCofinal`, `idomega_design.md` §2.4).

  The tower shapes (`omegaW_add_one_val`, `omegaTower_succ_val`) are what the bridge from the
  towers to their codes (`mc_omegaTower` in `IDn/UpperBound.lean`) rewrites with.
-/
import OrdinalAnalysis.IDw.ReductionAux

set_option autoImplicit false

namespace OrdinalAnalysis.IDw.Upper

open ThetaVTerm
open ThetaVNoteD (omegaTower)

/-! ### The shape of the towers -/

/-- `Ω_ω + 1 = ⟨Ω_ω, 0⟩`. -/
theorem omegaW_add_one_val :
    (ThetaVNoteD.OmegaW + ThetaVNoteD.one).1 = sum [OmegaW, sum []] := by
  show ofList (addL [OmegaW] [sum []]) = _
  have h : geb OmegaW (sum []) = true := by
    simp only [geb, decide_eq_true_eq]
    exact Or.inl (nil_lt_OmegaW)
  rw [addL_cons, List.filter_singleton, h]
  rfl

/-- The tower is a tower of sums. -/
theorem omegaTower_val :
    ∀ m, ∃ xs, (omegaTower m (ThetaVNoteD.OmegaW + ThetaVNoteD.one)).1 = sum xs
  | 0 => ⟨_, omegaW_add_one_val⟩
  | m + 1 => by
    obtain ⟨xs, hxs⟩ := omegaTower_val m
    refine ⟨[(omegaTower m (ThetaVNoteD.OmegaW + ThetaVNoteD.one)).1], ?_⟩
    show ofList [(omegaTower m (ThetaVNoteD.OmegaW + ThetaVNoteD.one)).1] = _
    rw [ofList_singleton_not_prin (by rw [hxs]; exact id)]

/-- `ω_{m+1}(Ω_ω + 1) = ⟨ω_m(Ω_ω + 1)⟩`. -/
theorem omegaTower_succ_val (m : ℕ) :
    (omegaTower (m + 1) (ThetaVNoteD.OmegaW + ThetaVNoteD.one)).1 =
      sum [(omegaTower m (ThetaVNoteD.OmegaW + ThetaVNoteD.one)).1] := by
  obtain ⟨xs, hxs⟩ := omegaTower_val m
  show ofList [(omegaTower m (ThetaVNoteD.OmegaW + ThetaVNoteD.one)).1] = _
  rw [ofList_singleton_not_prin (by rw [hxs]; exact id)]

/-- The term `ω_m(Ω_ω + 1)`. -/
abbrev tw (m : ℕ) : ThetaVTerm := (omegaTower m (ThetaVNoteD.OmegaW + ThetaVNoteD.one)).1

theorem tw_zero : tw 0 = sum [OmegaW, sum []] := omegaW_add_one_val

theorem tw_succ (m : ℕ) : tw (m + 1) = sum [tw m] := omegaTower_succ_val m

/-- `Ω_ω ≺ Ω_ω + 1`. -/
theorem OmegaW_lt_tw_zero : OmegaW < tw 0 := by
  rw [tw_zero]
  exact (OmegaW_lt_cons_iff _ _).mpr (le_refl' _)

/-- `ω_m(Ω_ω + 1)` is strictly increasing in `m`. -/
theorem tw_lt_tw_succ : ∀ m, tw m < tw (m + 1)
  | 0 => by
    rw [tw_succ, tw_zero, cons_lt_cons_iff]
    exact Or.inl (by rw [← tw_zero]; exact OmegaW_lt_tw_zero)
  | m + 1 => by
    rw [tw_succ (m + 1), tw_succ m, cons_lt_cons_iff]
    refine Or.inl ?_
    have := tw_lt_tw_succ m
    rwa [tw_succ] at this

theorem tw_lt_tw {m₁ m₂ : ℕ} (h : m₁ < m₂) : tw m₁ < tw m₂ := by
  induction h with
  | refl => exact tw_lt_tw_succ m₁
  | step _ ih => exact lt_trans' ih (tw_lt_tw_succ _)

theorem tw_le_tw {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) : tw m₁ ≤ tw m₂ := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact le_of_lt' (tw_lt_tw h)
  · exact le_refl' _

/-- `E_k(ω_m(Ω_ω + 1)) = ∅`: the tower has no `ϑ`-subterm. -/
theorem E_tw (k : ℕ) : ∀ m, E k (tw m) = []
  | 0 => by rw [tw_zero]; simp
  | m + 1 => by rw [tw_succ]; simp [E_tw k m]

/-- `ϑ₀(ω_m(Ω_ω + 1))` is increasing in `m` (clause (ii'), `E_0(ω_m(Ω_ω+1)) = ∅`). -/
theorem theta_tw_le_theta_tw {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) : theta 0 (tw m₁) ≤ theta 0 (tw m₂) := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact le_of_lt' (theta_lt_theta_of_lt (tw_lt_tw h) (by rw [E_tw]; simp))
  · exact le_refl' _

/-! ### A common bound -/

/-- A common bound for finitely many terms, for a property monotone in the bound. -/
theorem exists_bound {p : ThetaVTerm → ℕ → Prop} (hp : ∀ t m₁ m₂, m₁ ≤ m₂ → p t m₁ → p t m₂) :
    ∀ (xs : List ThetaVTerm), (∀ x ∈ xs, ∃ m, p x m) → ∃ N, ∀ x ∈ xs, p x N
  | [], _ => ⟨0, by simp⟩
  | y :: ys, h => by
    obtain ⟨m, hm⟩ := h y List.mem_cons_self
    obtain ⟨N, hN⟩ := exists_bound hp ys fun x hx => h x (List.mem_cons_of_mem y hx)
    refine ⟨max m N, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp x m _ (le_max_left m N) hm
    · exact hp x N _ (le_max_right m N) (hN x hx)

/-! ### The cofinality -/

/-- **Every normal term lies below some `ω_m(Ω_ω + 1)`.** -/
theorem lt_omegaTower : ∀ {t : ThetaVTerm}, NF t → ∃ m, t < tw m
  | Omega j, _ => ⟨0, lt_trans' (Omega_lt_OmegaW (i := j)) OmegaW_lt_tw_zero⟩
  | OmegaW, _ => ⟨0, OmegaW_lt_tw_zero⟩
  | theta j a, _ => ⟨0, lt_trans' (theta_lt_OmegaW (i := j) (a := a)) OmegaW_lt_tw_zero⟩
  | sum [], _ => ⟨0, lt_trans' nil_lt_OmegaW OmegaW_lt_tw_zero⟩
  | sum (x :: xs), hn => by
    have hxs : Desc (x :: xs) := hn.desc
    have hbound : ∀ y ∈ x :: xs, ∃ m, y < tw m := fun y hy =>
      lt_omegaTower (hn.of_mem hy)
    obtain ⟨N, hN⟩ := exists_bound
      (p := fun y m => y < tw m)
      (fun _ _ _ hmn h => lt_of_lt_of_le' h (tw_le_tw hmn))
      (x :: xs) hbound
    refine ⟨N + 1, ?_⟩
    rw [tw_succ]
    exact (sum_lt_singleton_iff (desc_iff_pairwise.mp hxs) _).mpr hN
termination_by t => l t
decreasing_by exact l_lt_of_mem hy

/-- **A normal term below `Ω₁` lies below some `ϑ₀(ω_m(Ω_ω + 1))`.** -/
theorem lt_theta0_tower : ∀ {t : ThetaVTerm}, NF t → t < Omega 0 →
    ∃ m, t < theta 0 (tw m)
  | Omega j, _, h => absurd ((Omega_lt_Omega_iff (i := j) (j := 0)).mp h) (Nat.not_lt_zero j)
  | OmegaW, _, h => absurd h (not_OmegaW_lt_Omega 0)
  | theta j d, hn, h => by
    have hj0 : j = 0 := Nat.le_zero.mp ((theta_lt_Omega_iff (i := j) (j := 0) (a := d)).mp h)
    subst hj0
    have hnd : NF d := hn.theta_arg
    obtain ⟨m₀, hm₀⟩ := lt_omegaTower hnd
    obtain ⟨N, hN⟩ := exists_bound
      (p := fun g m => g < theta 0 (tw m))
      (fun _ _ _ hmn h => lt_of_lt_of_le' h (theta_tw_le_theta_tw hmn))
      (E 0 d) fun g hg => lt_theta0_tower (NF.of_mem_E hnd hg) (lt_Omega_of_mem_E hg)
    refine ⟨max m₀ N, theta_lt_theta_of_lt ?_ fun g hg => ?_⟩
    · exact lt_of_lt_of_le' hm₀ (tw_le_tw (le_max_left m₀ N))
    · exact lt_of_lt_of_le' (hN g hg) (theta_tw_le_theta_tw (le_max_right m₀ N))
  | sum [], _, _ => ⟨0, nil_lt_theta 0 _⟩
  | sum (x :: xs), hn, h => by
    obtain ⟨m, hm⟩ := lt_theta0_tower (hn.of_mem List.mem_cons_self)
      ((cons_lt_Omega_iff 0 x xs).mp h)
    exact ⟨m, (cons_lt_theta_iff 0 x _ xs).mpr hm⟩
termination_by t => l t
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · simp; omega

/-- **Every countable notation lies below some `ϑ₀(ω_m(Ω_ω + 1))`**: the cofinality the upper
bound of `ID_ω` uses (`idomega_design.md` H0), the replacement of `IDn`'s per-level
`exists_lt_theta0_tower` together with `exists_lt_c_succ`. -/
theorem exists_lt_tower {a : ThetaVNoteD} (ha : a.1 < ThetaVTerm.Omega 0) :
    ∃ m, a.1 < ThetaVTerm.theta 0
      (omegaTower m (ThetaVNoteD.OmegaW + ThetaVNoteD.one)).1 :=
  lt_theta0_tower a.2.1 ha

end OrdinalAnalysis.IDw.Upper
