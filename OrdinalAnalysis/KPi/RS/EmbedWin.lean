module

public import OrdinalAnalysis.KPi.RS.EmbedTr

/-!
# The RS calculus, part 31: windows, valuations and the bridges for the rules of the Tait calculus

`trS lam N e γ` is the RS-sentence of the `ℒ_Ad`-formula `γ` (free variables `&x`, no bound variables)
under the valuation `e : ℕ → T`, cut off at `N` (`truncV`: `x ≥ N` is read as `L_0`):  the `D0`-context is
`Fin (N+1)` (the last slot is a dummy `L_0`).  Because every variable has a value (`winRho_vf`), the
translations at different windows differ only by presentation (`trD_sim`), and

* `trS_shift_sim` : `shift γ` at `(N, e)` is `γ` at `(N-1, e ∘ succ)`  (the rule `shift`);
* `trS_free_sim`  : `free φ` at `(N+1, b :: e)` is the body of `∀x φ` at the value `b` (the rule `all`);
* `trS_subst_sim` : `φ/[&x]` is the body of `∃x φ` at the value `e x` (the rule `exs`);
* `kD_trD_sub`, `rk_trD_le` : `k` and `rk` of the translations.
-/

@[expose] public section

open Ordinal FFL FFL.FirstOrder

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

open OrdinalAnalysis.KPi (LAd AdRel)

variable {R : Set Ordinal.{1}}

/-! ### windows -/

/-- the valuation cut off at `N`. -/
def truncV (N : ℕ) (e : ℕ → T) : ℕ → T := fun x => if x < N then e x else T.L 0

/-- the variable `x` as an index of the window `Fin (N+1)`. -/
def winVf (N : ℕ) : ℕ → Fin (N + 1) := fun x => if h : x < N then ⟨x, Nat.lt_succ_of_lt h⟩ else Fin.last N

/-- the environment of the window. -/
def winRho (N : ℕ) (e : ℕ → T) : Fin (N + 1) → T := fun i => truncV N e i.1

theorem winRho_vf (N : ℕ) (e : ℕ → T) (x : ℕ) : winRho N e (winVf N x) = truncV N e x := by
  unfold winRho winVf truncV
  by_cases h : x < N
  · simp [h]
  · simp [h]

/-- `b :: e`. -/
def consV (b : T) (e : ℕ → T) : ℕ → T
  | 0 => b
  | x + 1 => e x

/-- the RS-sentence of a formula under a valuation. -/
def trS (lam : Ordinal.{1}) (N : ℕ) (e : ℕ → T) (γ : Semiformula LAd ℕ 0) : RSS :=
  RSS.base (trD lam (Fin.elim0 : Fin 0 → Fin (N + 1)) (winVf N) γ) (winRho N e)

theorem trS_neg (lam : Ordinal.{1}) (N : ℕ) (e : ℕ → T) (γ : Semiformula LAd ℕ 0) :
    trS lam N e (∼γ) = (trS lam N e γ).neg := by
  unfold trS
  rw [trD_neg]
  rfl

/-! ### the bridges -/

theorem trD_shift (lam : Ordinal.{1}) {M : ℕ} (vb : Fin 0 → Fin M) (vf : ℕ → Fin M)
    (γ : Semiformula LAd ℕ 0) :
    trD lam vb vf (Rewriting.shift γ) = trD lam vb (fun x => vf (x + 1)) γ := by
  have := trD_rew lam (Rew.shift : SyntacticRew LAd 0 0) vb vf γ
  rw [show Rewriting.shift γ = Rew.shift ▹ γ from rfl, this]
  congr 1

theorem trS_shift_sim (lam : Ordinal.{1}) (N : ℕ) (e : ℕ → T) (γ : Semiformula LAd ℕ 0) :
    Sim R (trS lam (N - 1) (fun x => e (x + 1)) γ) (trS lam N e (Rewriting.shift γ)) := by
  unfold trS
  rw [trD_shift]
  refine trD_sim lam _ _ _ _ _ _ γ (fun i => i.elim0) (fun x _ => ?_)
  rw [winRho_vf, winRho_vf]
  unfold truncV
  by_cases h : x + 1 < N
  · have h' : x < N - 1 := by omega
    simp [h, h']
  · have h' : ¬ x < N - 1 := by omega
    simp [h, h']

theorem trD_free (lam : Ordinal.{1}) {M : ℕ} (vf : ℕ → Fin M) (φ : Semiformula LAd ℕ 1) :
    trD lam (Fin.elim0 : Fin 0 → Fin M) vf (Rewriting.free φ) =
      trD lam (fun _ => vf 0) (fun x => vf (x + 1)) φ := by
  have := trD_rew lam (Rew.free : SyntacticRew LAd 1 0) (Fin.elim0 : Fin 0 → Fin M) vf φ
  rw [show Rewriting.free φ = Rew.free ▹ φ from rfl, this]
  congr 1
  funext i
  have : i = 0 := Fin.ext (by have := i.2; omega)
  subst this
  simp [evT, Rew.free]

theorem trS_free_sim (lam : Ordinal.{1}) (N : ℕ) (e : ℕ → T) (b : T) (φ : Semiformula LAd ℕ 1) :
    Sim R (trS lam (N + 1) (consV b e) (Rewriting.free φ))
      (RSS.base (trD lam (extV (Fin.elim0 : Fin 0 → Fin (N + 1))) (liftVf (winVf N)) φ)
        (ext (winRho N e) b)) := by
  unfold trS
  rw [trD_free]
  refine trD_sim lam _ _ _ _ _ _ φ (fun i => ?_) (fun x _ => ?_)
  · have : i = 0 := Fin.ext (by have := i.2; omega)
    subst this
    simp [winRho, winVf, truncV, consV]
  · rw [winRho_vf]
    simp only [liftVf]
    rw [ext_castSucc, winRho_vf]
    simp [truncV, consV]

theorem trD_subst (lam : Ordinal.{1}) {M : ℕ} (vf : ℕ → Fin M) (x : ℕ) (φ : Semiformula LAd ℕ 1) :
    trD lam (Fin.elim0 : Fin 0 → Fin M) vf (φ ⇜ ![(&x : Semiterm LAd ℕ 0)]) =
      trD lam (fun _ => vf x) vf φ := by
  have := trD_rew lam (Rew.subst ![(&x : Semiterm LAd ℕ 0)] : Rew LAd ℕ 1 ℕ 0)
    (Fin.elim0 : Fin 0 → Fin M) vf φ
  rw [show (φ ⇜ ![(&x : Semiterm LAd ℕ 0)]) = Rew.subst ![(&x : Semiterm LAd ℕ 0)] ▹ φ from rfl, this]
  congr 1
  funext i
  have : i = 0 := Fin.ext (by have := i.2; omega)
  subst this
  simp [evT]

theorem trS_subst_sim (lam : Ordinal.{1}) (N : ℕ) (e : ℕ → T) (x : ℕ) (φ : Semiformula LAd ℕ 1) :
    Sim R (trS lam N e (φ ⇜ ![(&x : Semiterm LAd ℕ 0)]))
      (RSS.base (trD lam (extV (Fin.elim0 : Fin 0 → Fin (N + 1))) (liftVf (winVf N)) φ)
        (ext (winRho N e) (truncV N e x))) := by
  unfold trS
  rw [trD_subst]
  refine trD_sim lam _ _ _ _ _ _ φ (fun i => ?_) (fun y _ => ?_)
  · have : i = 0 := Fin.ext (by have := i.2; omega)
    subst this
    simp [winRho_vf]
  · simp only [liftVf]
    rw [ext_castSucc]


/-! ### valuations, `k` and `rk` of the translations -/

/-- all values are terms of level `< lam`. -/
def Val (lam : Ordinal.{1}) (e : ℕ → T) : Prop := ∀ x, (e x).level < lam

theorem Val.trunc {lam : Ordinal.{1}} (hlam : 0 < lam) {e : ℕ → T} (h : Val lam e) (N : ℕ) :
    Val lam (truncV N e) := by
  intro x
  unfold truncV
  by_cases hx : x < N
  · simp [hx, h x]
  · simp [hx, T.L, T.level, PT.level, hlam]

theorem Val.cons {lam : Ordinal.{1}} {e : ℕ → T} (h : Val lam e) {b : T} (hb : b.level < lam) :
    Val lam (consV b e) := by
  intro x
  cases x with
  | zero => exact hb
  | succ x => exact h x

theorem Val.win {lam : Ordinal.{1}} (hlam : 0 < lam) {e : ℕ → T} (h : Val lam e) (N : ℕ)
    (i : Fin (N + 1)) : (winRho N e i).level < lam :=
  Val.trunc hlam h N i.1

/-- the set of levels occurring in an environment. -/
def Kenv {M : ℕ} (ρ : Fin M → T) : Set Ordinal.{1} := {ξ | ∃ i, ξ ∈ (ρ i).k}

theorem kD_trD_sub (lam : Ordinal.{1}) : ∀ {k M : ℕ} (vb : Fin k → Fin M) (vf : ℕ → Fin M)
    (e : Fin M → Set Ordinal.{1}) (φ : Semiformula LAd ℕ k),
    ∀ ξ ∈ kD (trD lam vb vf φ) e, (∃ i, ξ ∈ e i) ∨ ξ = lam ∨ ξ = 0 := by
  intro k M vb vf e φ
  induction φ using Semiformula.rec' generalizing M e with
  | hverum => intro ξ hξ; simp [trD, kD, kBd] at hξ; exact Or.inr (Or.inr hξ)
  | hfalsum => intro ξ hξ; simp [trD, kD, kBd] at hξ; exact Or.inr (Or.inr hξ)
  | hrel r v =>
    intro ξ hξ
    cases r
    · simp only [trD, kD] at hξ
      rcases hξ with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inl ⟨_, h⟩
    · simp only [trD, kD] at hξ
      exact Or.inl ⟨_, hξ⟩
  | hnrel r v =>
    intro ξ hξ
    cases r
    · simp only [trD, kD] at hξ
      rcases hξ with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inl ⟨_, h⟩
    · simp only [trD, kD] at hξ
      exact Or.inl ⟨_, hξ⟩
  | hand φ ψ ihφ ihψ =>
    intro ξ hξ
    simp only [trD, kD] at hξ
    rcases hξ with h | h
    · exact ihφ vb vf e ξ h
    · exact ihψ vb vf e ξ h
  | hor φ ψ ihφ ihψ =>
    intro ξ hξ
    simp only [trD, kD] at hξ
    rcases hξ with h | h
    · exact ihφ vb vf e ξ h
    · exact ihψ vb vf e ξ h
  | hall φ ih =>
    intro ξ hξ
    simp only [trD, kD, kBd] at hξ
    rcases hξ with h | h
    · exact Or.inr (Or.inl h)
    · rcases ih (extV vb) (liftVf vf) (ext e ∅) ξ h with ⟨i, hi⟩ | h
      · induction i using Fin.lastCases with
        | last => simp at hi
        | cast j => exact Or.inl ⟨j, by simpa using hi⟩
      · exact Or.inr h
  | hexs φ ih =>
    intro ξ hξ
    simp only [trD, kD, kBd] at hξ
    rcases hξ with h | h
    · exact Or.inr (Or.inl h)
    · rcases ih (extV vb) (liftVf vf) (ext e ∅) ξ h with ⟨i, hi⟩ | h
      · induction i using Fin.lastCases with
        | last => simp at hi
        | cast j => exact Or.inl ⟨j, by simpa using hi⟩
      · exact Or.inr h

theorem trS_k_sub (lam : Ordinal.{1}) (N : ℕ) (e : ℕ → T) (γ : Semiformula LAd ℕ 0) :
    ∀ ξ ∈ (trS lam N e γ).k, ξ ∈ Kenv (winRho N e) ∨ ξ = lam ∨ ξ = 0 := by
  intro ξ hξ
  exact kD_trD_sub lam _ _ _ γ ξ hξ

theorem rk_trD_le (lam : Ordinal.{1}) : ∀ {k : ℕ} (φ : Semiformula LAd ℕ k), ∃ n : ℕ,
    ∀ {M : ℕ} (vb : Fin k → Fin M) (vf : ℕ → Fin M) (e : Fin M → Ordinal.{1}) (B : Ordinal.{1}),
      ω * lam ≤ B → (∀ i, e i ≤ B) → rkD (trD lam vb vf φ) e ≤ B + n := by
  intro k φ
  induction φ using Semiformula.rec' with
  | hverum =>
    refine ⟨8, fun {M} vb vf e B hB he => ?_⟩
    simp only [trD, rkD, rkBd, mul_zero, ext_last, zero_add]
    refine max_le (zero_le) ?_
    have h6 : max (6 : Ordinal.{1}) 1 = 6 := max_eq_left (by norm_num)
    rw [h6]
    exact (by norm_num : (6 : Ordinal.{1}) + 2 ≤ 8).trans le_add_self
  | hfalsum =>
    refine ⟨8, fun {M} vb vf e B hB he => ?_⟩
    simp only [trD, rkD, rkBd, mul_zero, ext_last, zero_add]
    refine max_le (zero_le) ?_
    have h6 : max (6 : Ordinal.{1}) 1 = 6 := max_eq_left (by norm_num)
    rw [h6]
    exact (by norm_num : (6 : Ordinal.{1}) + 2 ≤ 8).trans le_add_self
  | hrel r v =>
    refine ⟨6, fun {M} vb vf e B hB he => ?_⟩
    cases r
    · simp only [trD, rkD]
      refine max_le ?_ ?_
      · exact addR_le (he _) 6
      · exact (addR_le (he _) 1).trans (addL_le B (by norm_num))
    · simp only [trD, rkD]
      exact (addR_le (he _) 5).trans (addL_le B (by norm_num))
  | hnrel r v =>
    refine ⟨6, fun {M} vb vf e B hB he => ?_⟩
    cases r
    · simp only [trD, rkD]
      refine max_le ?_ ?_
      · exact addR_le (he _) 6
      · exact (addR_le (he _) 1).trans (addL_le B (by norm_num))
    · simp only [trD, rkD]
      exact (addR_le (he _) 5).trans (addL_le B (by norm_num))
  | hand φ ψ ihφ ihψ =>
    obtain ⟨n1, h1⟩ := ihφ
    obtain ⟨n2, h2⟩ := ihψ
    refine ⟨max n1 n2 + 1, fun {M} vb vf e B hB he => ?_⟩
    simp only [trD, rkD]
    have c1 : (n1 : Ordinal.{1}) ≤ ((max n1 n2 : ℕ) : Ordinal.{1}) := by exact_mod_cast le_max_left n1 n2
    have a1 := (h1 vb vf e B hB he).trans (addL_le B c1)
    have c2 : (n2 : Ordinal.{1}) ≤ ((max n1 n2 : ℕ) : Ordinal.{1}) := by exact_mod_cast le_max_right n1 n2
    have a2 := (h2 vb vf e B hB he).trans (addL_le B c2)
    calc max (rkD (trD lam vb vf φ) e) (rkD (trD lam vb vf ψ) e) + 1
        ≤ B + (max n1 n2 : ℕ) + 1 := addR_le (max_le a1 a2) 1
      _ = B + ((max n1 n2 + 1 : ℕ) : Ordinal.{1}) := by push_cast; rw [add_assoc]
  | hor φ ψ ihφ ihψ =>
    obtain ⟨n1, h1⟩ := ihφ
    obtain ⟨n2, h2⟩ := ihψ
    refine ⟨max n1 n2 + 1, fun {M} vb vf e B hB he => ?_⟩
    simp only [trD, rkD]
    have c1 : (n1 : Ordinal.{1}) ≤ ((max n1 n2 : ℕ) : Ordinal.{1}) := by exact_mod_cast le_max_left n1 n2
    have a1 := (h1 vb vf e B hB he).trans (addL_le B c1)
    have c2 : (n2 : Ordinal.{1}) ≤ ((max n1 n2 : ℕ) : Ordinal.{1}) := by exact_mod_cast le_max_right n1 n2
    have a2 := (h2 vb vf e B hB he).trans (addL_le B c2)
    calc max (rkD (trD lam vb vf φ) e) (rkD (trD lam vb vf ψ) e) + 1
        ≤ B + (max n1 n2 : ℕ) + 1 := addR_le (max_le a1 a2) 1
      _ = B + ((max n1 n2 + 1 : ℕ) : Ordinal.{1}) := by push_cast; rw [add_assoc]
  | hall φ ih =>
    obtain ⟨n, h⟩ := ih
    refine ⟨n + 2, fun {M} vb vf e B hB he => ?_⟩
    simp only [trD, rkD, rkBd]
    refine max_le (hB.trans le_self_add) ?_
    have := (h (extV vb) (liftVf vf) (ext e 0) B hB (ext_zero_le he)).trans le_rfl
    calc rkD (trD lam (extV vb) (liftVf vf) φ) (ext e 0) + 2 ≤ B + n + 2 := addR_le this 2
      _ = B + ((n + 2 : ℕ) : Ordinal.{1}) := by push_cast; rw [add_assoc]
  | hexs φ ih =>
    obtain ⟨n, h⟩ := ih
    refine ⟨n + 2, fun {M} vb vf e B hB he => ?_⟩
    simp only [trD, rkD, rkBd]
    refine max_le (hB.trans le_self_add) ?_
    have := (h (extV vb) (liftVf vf) (ext e 0) B hB (ext_zero_le he)).trans le_rfl
    calc rkD (trD lam (extV vb) (liftVf vf) φ) (ext e 0) + 2 ≤ B + n + 2 := addR_le this 2
      _ = B + ((n + 2 : ℕ) : Ordinal.{1}) := by push_cast; rw [add_assoc]

theorem T.rk_le_of_level_lt {lam : Ordinal.{1}} (hmul : ω * lam = lam) {t : T}
    (h : t.level < lam) : t.rk ≤ lam := by
  have h1 := T.rk_lt t
  have h2 : ω * (t.level + 1) ≤ ω * lam := mul_le_mul_right (Order.add_one_le_of_lt h) ω
  rw [hmul] at h2
  exact (h1.trans_le h2).le

theorem rk_trS_le (lam : Ordinal.{1}) (hmul : ω * lam = lam) (hlam : 0 < lam)
    (γ : Semiformula LAd ℕ 0) : ∃ n : ℕ, ∀ (N : ℕ) (e : ℕ → T), Val lam e →
      (trS lam N e γ).rk ≤ lam + n := by
  obtain ⟨n, hn⟩ := rk_trD_le lam γ
  refine ⟨n, fun N e he => ?_⟩
  exact hn Fin.elim0 (winVf N) (fun i => (winRho N e i).rk) lam hmul.le
    (fun i => T.rk_le_of_level_lt hmul (Val.win hlam he N i))

end OrdinalAnalysis.KPi.RS
