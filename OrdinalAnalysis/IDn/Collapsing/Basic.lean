/-
  Vocabulary and small facts for the multi-level collapsing theorem
  (`IDn/Collapsing/Statement.lean`), all proved (no `sorry`).

  Source: W. Buchholz, *A simplified version of local predicativity*, in: P. Aczel,
  H. Simmons, S. Wainer (eds.), *Proof Theory* (Leeds 1990), CUP 1992, p. 26 (Lemma 4.6, the
  set `K̄ = {Ω̄_σ}` with `Ω̄_σ = Ω_σ + 1` for regular `Ω_σ`, the hypothesis `𝒜(Θ; γ, κ, μ)`,
  Lemma 4.7 (𝒜1)–(𝒜4)); A. Freund, arXiv:2204.09321, Theorem 6.7 (one level).

  Contents.

    `muBar m`                 `Ω̄_m`: `0` for `m = 0`, `Ω_m + 1` (Lean `Omega (m-1) + 1`) else
    `psi k`                   `ψ_κ`, `κ = Ω_{k+1}`: `ϑ_k` = `(Notn.thetaWLevel k).theta`
    `hat γ μ α`               `α̂ := γ + ω^{μ+μ+α}` (Buchholz 4.8's `γ + ω^{μ+α}`, doubled `μ`)
    `Hg γ X`                  `H_γ[Θ]` with `k(Θ) = X`: `adjoin (HopS γ) X`
    `capSeq k b Γ`            the level-`k` cap `Γ^b` of a sequent
    the (𝒜1)–(𝒜4) facts       `hat_mem`, `dom_hat`, `psi_hat_mem`, `lt_psi_hat`, …
    `sigmaW_mono`             `Σ(Ω_{k+1}) ⊆ Σ(Ω_{p+1})` for `k ≤ p`
    `sigmaW_unfold_le`        `A_j(t, I_j^{≺g})`, `j ≤ k`, and its negation are `Σ(Ω_{k+1})`
    `le_of_lt_add_one_col`    `α ≺ β + 1 ⇒ α ⪯ β`
    `rk_eq_Omega_cases`       the formulas of rank `Ω_{p+1}`: `±I_p t`, `±I_{p+1}^{≺0} t`
    `drop_stage_zero`         the empty disjunction `I_j^{≺0} t` can be dropped from a sequent
-/
import OrdinalAnalysis.IDn.Calculus
import OrdinalAnalysis.Ordinal.Collapsing.ThetaWInstance

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

/-- If `⟨xs⟩ ≺ ⟨ys, 0⟩` then not `⟨ys⟩ ≺ ⟨xs⟩` (ported from `ID1/ReductionAux.lean`). -/
theorem not_lt_of_lt_append_zero_col : ∀ (ys xs : List ThetaWTerm),
    sum xs < sum (ys ++ [sum []]) → ¬ sum ys < sum xs
  | [], [], _, h2 => not_nil_lt_nil h2
  | [], x :: xs, h1, _ => by
    rcases (cons_lt_cons_iff (a := x) (b := sum []) (as := xs) (bs := [])).mp h1 with h | ⟨-, h⟩
    · exact not_lt_nil x h
    · exact not_lt_nil _ h
  | _ :: _, [], _, h2 => not_cons_lt_nil _ _ h2
  | y :: ys, x :: xs, h1, h2 => by
    rw [List.cons_append] at h1
    rcases (cons_lt_cons_iff (a := x) (b := y) (as := xs) (bs := _)).mp h1 with h | ⟨rfl, h⟩
    · rcases (cons_lt_cons_iff (a := y) (b := x) (as := ys) (bs := xs)).mp h2 with h' | ⟨rfl, -⟩
      · exact lt_asymm' h h'
      · exact lt_irrefl' _ h
    · rcases (cons_lt_cons_iff (a := x) (b := x) (as := ys) (bs := xs)).mp h2 with h' | ⟨-, h'⟩
      · exact lt_irrefl' _ h'
      · exact not_lt_of_lt_append_zero_col ys xs h h'

end ThetaWTerm

namespace IDn

namespace Collapsing

open LO LO.FirstOrder

variable {n : ℕ}

/-! ### Ordinal vocabulary -/

/-- `α ≺ β + 1` gives `α ⪯ β`. -/
theorem le_of_lt_add_one_col {a b : ThetaWNoteD} (h : a < b + ThetaWNoteD.one) : a ≤ b := by
  rw [ThetaWNoteD.add_one_eq_succ] at h
  refine le_of_not_gt fun hba => ?_
  rw [ThetaWNoteD.lt_iff_entries, ThetaWNoteD.succ, ThetaWNoteD.entries_nadd_one] at h
  exact ThetaWTerm.not_lt_of_lt_append_zero_col _ _ h (ThetaWNoteD.lt_iff_entries.mp hba)

/-- **`Ω̄_m`** (Buchholz p. 26, `K̄ = {Ω̄_σ}`), for the regulars `Ω_1, Ω_2, …` of `ThetaWNoteD`
and `Ω_0 := 0` (not regular): `Ω̄_0 = 0`, `Ω̄_m = Ω_m + 1` for `m ≥ 1`.  Lean's `Omega s` is
`Ω_{s+1}`, so `muBar (s+1) = Omega s + 1`. -/
def muBar : ℕ → ThetaWNoteD
  | 0 => ThetaWNoteD.zero
  | s + 1 => ThetaWNoteD.Omega s + ThetaWNoteD.one

@[simp] theorem muBar_zero : muBar 0 = ThetaWNoteD.zero := rfl

@[simp] theorem muBar_succ (s : ℕ) : muBar (s + 1) = ThetaWNoteD.Omega s + ThetaWNoteD.one := rfl

/-- **`ψ_κ` at `κ = Ω_{k+1}`**: the collapsing function `ϑ_k` of the merged interface
(`Notn.thetaWLevel k`, total, junk `0` outside its domain `DomK k`). -/
noncomputable def psi (k : ℕ) (a : ThetaWNoteD) : ThetaWNoteD := (Notn.thetaWLevel k).theta a

/-- **`α̂ := γ + ω^{μ+μ+α}`**: Buchholz's Theorem 4.8 has `γ + ω^{μ+α}`.  The exponent carries
`μ` twice so that in the step (□) the base `γ' ⪰ ω^{μ+μ} ⪰ ω^{Ω_{σ+1}·2}` exceeds every argument
`Ω_{σ+1}·ρ + β` (`ρ, β ≺ Ω_{σ+1}`) of the syntactic Veblen function `φ_σ(ρ, β) = ϑ_σ(Ω_{σ+1}·ρ + β)`:
`HopS` is closed under `ϑ_σ` only on arguments `⪯ γ'` (`theta_mem_HopS`), unlike Buchholz's `H_γ`,
which is closed under `φ` by definition (Lemma 4.6 b)).  Audit the design notes item 1. -/
def hat (γ μ α : ThetaWNoteD) : ThetaWNoteD := γ + ThetaWNoteD.omegaPow (μ + μ + α)

/-- **`H_γ[Θ]`**, `k(Θ) = X`: the level-free Buchholz operator `H_γ` (`HopS γ`) with `X`
adjoined. -/
def Hg (γ : ThetaWNoteD) (X : Set ThetaWNoteD) : Set ThetaWNoteD → Set ThetaWNoteD :=
  ThetaWNoteD.adjoin (ThetaWNoteD.HopS γ) X

/-- **The level-`k` cap of a sequent**, `Γ^b` (Freund's `Γ^β`, Buchholz's `Γ^β`, at level
`k`): every `I_k^{≺Ω_{k+1}}` replaced by `I_k^{≺b}`. -/
def capSeq (k : Fin n) (b : StageAt k.val) (Γ : Sequent (LIinfN n)) : Sequent (LIinfN n) :=
  Γ.map (capAt k b)

@[simp] theorem capSeq_singleton (k : Fin n) (b : StageAt k.val) (φ : Proposition (LIinfN n)) :
    capSeq k b [φ] = [capAt k b φ] := rfl

/-! ### The operator `H_γ[Θ]` -/

theorem Hg_empty (γ : ThetaWNoteD) (X : Set ThetaWNoteD) :
    Hg γ X ∅ = ThetaWNoteD.HopS γ X := by
  simp [Hg, ThetaWNoteD.adjoin]

theorem Hg_niceS (γ : ThetaWNoteD) (X : Set ThetaWNoteD) : ThetaWNoteD.NiceS (Hg γ X) :=
  (ThetaWNoteD.HopS_nice γ).adjoin X

theorem Hg_isOperator (γ : ThetaWNoteD) (X : Set ThetaWNoteD) : ThetaWNoteD.IsOperator (Hg γ X) :=
  (Hg_niceS γ X).1

theorem Hg_mono {γ γ' : ThetaWNoteD} (h : γ ≤ γ') (X : Set ThetaWNoteD) :
    ∀ Z, Hg γ X Z ⊆ Hg γ' X Z :=
  fun _ => ThetaWNoteD.HopS_subset_HopS_of_le h _

theorem Hg_adjoin (γ : ThetaWNoteD) (X Z : Set ThetaWNoteD) :
    ThetaWNoteD.adjoin (Hg γ X) Z = Hg γ (X ∪ Z) :=
  ThetaWNoteD.adjoin_adjoin _ _ _

theorem mem_Hg_empty {γ x : ThetaWNoteD} {X : Set ThetaWNoteD} :
    x ∈ Hg γ X ∅ ↔ x ∈ ThetaWNoteD.HopS γ X := by rw [Hg_empty]

/-! ### Membership, domain and comparison facts (Buchholz, Lemma 4.7 (𝒜1)–(𝒜4)) -/

section Facts

variable {k : ℕ} {γ : ThetaWNoteD} {X : Set ThetaWNoteD}

theorem muBar_mem (m : ℕ) (a : ThetaWNoteD) : muBar m ∈ ThetaWNoteD.HopS a X := by
  cases m with
  | zero => exact (ThetaWNoteD.HopS_nice a).zero_mem
  | succ s =>
    exact (ThetaWNoteD.HopS_nice a).add_mem ((ThetaWNoteD.HopS_nice a).Omega_mem s)
      (ThetaWNoteD.HopS_nice a).one_mem

theorem muBar_mono {a b : ℕ} (h : a ≤ b) : muBar a ≤ muBar b := by
  cases a with
  | zero => exact ThetaWNoteD.zero_le' _
  | succ a =>
    cases b with
    | zero => exact absurd h (Nat.not_succ_le_zero a)
    | succ b =>
      rw [muBar_succ, muBar_succ, ThetaWNoteD.add_one_eq_succ, ThetaWNoteD.add_one_eq_succ]
      refine ThetaWNoteD.succ_le_succ ?_
      rcases Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ h) with h' | rfl
      · exact le_of_lt (ThetaWNoteD.Omega_lt_Omega_iff.mpr h')
      · exact le_rfl

/-- `Ω̄_p ≺ Ω_{p+1}` (Lean `Omega p`). -/
theorem muBar_lt_Omega (p : ℕ) : muBar p < ThetaWNoteD.Omega p := by
  cases p with
  | zero => exact ThetaWNoteD.zero_lt_Omega 0
  | succ s =>
    rw [muBar_succ, ThetaWNoteD.add_one_eq_succ]
    exact ThetaWNoteD.succ_lt_prin trivial (ThetaWNoteD.Omega_lt_Omega_iff.mpr (Nat.lt_succ_self s))

/-- `Ω_{p+1} ⪯ Ω̄_m` for `p < m`: a regular `π ≺ μ`. -/
theorem Omega_le_muBar {p m : ℕ} (h : p < m) : ThetaWNoteD.Omega p ≤ muBar m := by
  cases m with
  | zero => exact absurd h (Nat.not_lt_zero p)
  | succ m =>
    rw [muBar_succ]
    refine le_trans ?_ (ThetaWNoteD.le_add_right _ _)
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | rfl
    · exact le_of_lt (ThetaWNoteD.Omega_lt_Omega_iff.mpr h')
    · exact le_rfl

theorem hat_lt_hat (γ μ : ThetaWNoteD) {α₀ α : ThetaWNoteD} (h : α₀ < α) :
    hat γ μ α₀ < hat γ μ α :=
  ThetaWNoteD.add_lt_add_left γ
    (ThetaWNoteD.omegaPow_lt_omegaPow (ThetaWNoteD.add_lt_add_left (μ + μ) h))

theorem gamma_lt_hat (γ μ α : ThetaWNoteD) : γ < hat γ μ α :=
  ThetaWNoteD.lt_add_omegaPow_hull γ (μ + μ + α)

theorem gamma_le_hat (γ μ α : ThetaWNoteD) : γ ≤ hat γ μ α := le_of_lt (gamma_lt_hat γ μ α)

/-- The exponent `μ + μ + α` lies in `H_γ[Θ]`. -/
theorem exp_mem {m : ℕ} {α : ThetaWNoteD} (hα : α ∈ ThetaWNoteD.HopS γ X) :
    muBar m + muBar m + α ∈ ThetaWNoteD.HopS γ X :=
  (ThetaWNoteD.HopS_nice γ).add_mem
    ((ThetaWNoteD.HopS_nice γ).add_mem (muBar_mem m γ) (muBar_mem m γ)) hα

/-- (𝒜1), first half: `α̂ ∈ H_{α̂}[Θ]`. -/
theorem hat_mem {m : ℕ} {α : ThetaWNoteD} (hγ : γ ∈ ThetaWNoteD.HopS γ X)
    (hα : α ∈ ThetaWNoteD.HopS γ X) : hat γ (muBar m) α ∈ ThetaWNoteD.HopS (hat γ (muBar m) α) X :=
  ThetaWNoteD.add_omegaPow_mem_HopS hγ (exp_mem hα)

/-- `α̂ ∈ H_γ[Θ]`. -/
theorem hat_mem_self {m : ℕ} {α : ThetaWNoteD} (hγ : γ ∈ ThetaWNoteD.HopS γ X)
    (hα : α ∈ ThetaWNoteD.HopS γ X) : hat γ (muBar m) α ∈ ThetaWNoteD.HopS γ X :=
  (ThetaWNoteD.HopS_nice γ).add_mem hγ ((ThetaWNoteD.HopS_nice γ).omegaPow_mem (exp_mem hα))

/-- The domain side condition of `ϑ_k` at `α̂` (`HullDom.dom_add_omegaPow`, through the
interface field `dom_add_omegaPow`). -/
theorem dom_hat {m : ℕ} {α : ThetaWNoteD} (hX : ThetaWNoteD.HullHypGe k γ X)
    (hγ : γ ∈ ThetaWNoteD.HopS γ X) (hα : α ∈ ThetaWNoteD.HopS γ X) :
    (Notn.thetaWLevel k).D (hat γ (muBar m) α) :=
  (Notn.thetaWLevel k).dom_add_omegaPow (a := γ) (b := muBar m + muBar m + α) hX hγ (exp_mem hα)

/-- (𝒜1), second half: `ψ_κ α̂ ∈ H_{α̂}[Θ]` (Buchholz's (1) in the proof of Theorem 4.8). -/
theorem psi_hat_mem {m : ℕ} {α : ThetaWNoteD} (hX : ThetaWNoteD.HullHypGe k γ X)
    (hγ : γ ∈ ThetaWNoteD.HopS γ X) (hα : α ∈ ThetaWNoteD.HopS γ X) :
    psi k (hat γ (muBar m) α) ∈ ThetaWNoteD.HopS (hat γ (muBar m) α) X :=
  (Notn.thetaWLevel k).theta_add_omegaPow_mem_Hop (a := γ) (b := muBar m + muBar m + α) hX hγ
    (exp_mem hα)

theorem psi_lt_Omega (k : ℕ) (a : ThetaWNoteD) : psi k a < ThetaWNoteD.Omega k :=
  (Notn.thetaWLevel k).theta_lt_Omega a

/-- (𝒜3): `H_γ[Θ] ∩ Ω_{k+1} ⊆ ψ_k(α̂)`. -/
theorem lt_psi_hat {m : ℕ} {α d : ThetaWNoteD} (hX : ThetaWNoteD.HullHypGe k γ X)
    (hγ : γ ∈ ThetaWNoteD.HopS γ X) (hα : α ∈ ThetaWNoteD.HopS γ X)
    (hd : d ∈ ThetaWNoteD.HopS γ X) (hdΩ : d < ThetaWNoteD.Omega k) :
    d < psi k (hat γ (muBar m) α) :=
  (Notn.thetaWLevel k).hullHyp_lt_theta hX (gamma_lt_hat γ _ α) (dom_hat hX hγ hα) hd hdΩ

/-- Buchholz's (2) in the proof of Theorem 4.8 (from (𝒜2)): `α₀ ≺ α`, `α₀ ∈ H_γ[Θ]` give
`ψ_κ α̂₀ ≺ ψ_κ α̂`. -/
theorem psi_hat_lt_psi_hat {m : ℕ} {α₀ α : ThetaWNoteD} (hX : ThetaWNoteD.HullHypGe k γ X)
    (hγ : γ ∈ ThetaWNoteD.HopS γ X) (hα₀ : α₀ ∈ ThetaWNoteD.HopS γ X)
    (hα : α ∈ ThetaWNoteD.HopS γ X) (h : α₀ < α) :
    psi k (hat γ (muBar m) α₀) < psi k (hat γ (muBar m) α) :=
  (Notn.thetaWLevel k).theta_lt_theta_add (a := γ) (b := muBar m + muBar m + α)
    (b' := muBar m + muBar m + α₀) hX hγ
    (exp_mem hα) (exp_mem hα₀) (ThetaWNoteD.add_lt_add_left _ h)

/-- A general comparison: `γ ⪯ x ≺ y`, `x ∈ H_γ[Θ]`, both in the domain, give
`ψ_k x ≺ ψ_k y` (Freund, Proposition 3.11 (c), through the interface). -/
theorem psi_lt_psi {x y : ThetaWNoteD} (hX : ThetaWNoteD.HullHypGe k γ X) (hγx : γ ≤ x)
    (hxy : x < y) (hx : x ∈ ThetaWNoteD.HopS γ X) (hDx : (Notn.thetaWLevel k).D x)
    (hDy : (Notn.thetaWLevel k).D y) : psi k x < psi k y :=
  (Notn.thetaWLevel k).theta_lt_theta_of_mem_Hop hX hγx hxy hx hDx hDy

/-- `ψ_k` of a domain point is principal, hence positive, and above `Ω_k` (Lean
`OmegaBelow k`). -/
theorem OmegaBelow_lt_psi {a : ThetaWNoteD} (hD : (Notn.thetaWLevel k).D a) :
    ThetaWNoteD.OmegaBelow k < psi k a := by
  cases k with
  | zero =>
    have hp : ThetaWTerm.IsPrin (psi 0 a).1 := (Notn.thetaWLevel 0).isPrin_theta hD
    exact lt_trans ThetaWNoteD.zero_lt_one (ThetaWNoteD.one_lt_prin hp)
  | succ s => exact Notn.thetaWTower.Omega_lt_theta_succ s a hD

theorem Omega_le_psi {j : ℕ} (hjk : j < k) {a : ThetaWNoteD} (hD : (Notn.thetaWLevel k).D a) :
    ThetaWNoteD.Omega j ≤ psi k a :=
  le_trans (ThetaWNoteD.Omega_le_OmegaBelow_of_lt hjk) (le_of_lt (OmegaBelow_lt_psi hD))

end Facts

/-! ### `Σ(Ω_{k+1})` -/

section Sigma

variable {ξ : Type*} {m : ℕ}

/-- **`Σ(Ω_{k+1}) ⊆ Σ(Ω_{p+1})` for `k ≤ p`.** -/
theorem sigmaW_mono {k p : Fin n} (hkp : k.val ≤ p.val) {φ : Semiformula (LIinfN n) ξ m}
    (h : SigmaW k φ) : SigmaW p φ := by
  induction φ using Semiformula.rec' with
  | hverum => trivial
  | hfalsum => trivial
  | hrel r v =>
    rcases r with r | r
    · trivial
    · cases r with
      | X => trivial
      | stage s => exact le_trans (h : s.lvl.val ≤ k.val) hkp
  | hnrel r v =>
    rcases r with r | r
    · trivial
    · cases r with
      | X => trivial
      | stage s =>
        obtain ⟨h1, h2⟩ := (h : s.lvl.val ≤ k.val ∧ s ≠ Stage.top k)
        refine ⟨le_trans h1 hkp, fun e => h2 ?_⟩
        have hl : s.lvl = p := by rw [e, Stage.lvl_top]
        have hpk : p = k := Fin.ext (le_antisymm (hl ▸ h1) hkp)
        rw [e, hpk]
  | hand φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | hor φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | hall φ ih => exact ih h
  | hexs φ ih => exact ih h

theorem sigmaW_mono_seq {k p : Fin n} (hkp : k.val ≤ p.val) {Γ : Sequent (LIinfN n)}
    (h : ∀ φ ∈ Γ, SigmaW k φ) : ∀ φ ∈ Γ, SigmaW p φ :=
  fun φ hφ => sigmaW_mono hkp (h φ hφ)

/-- **`A_j(t, I_j^{≺g})` and its negation are `Σ(Ω_{k+1})`** for `j ≤ k`, provided the stage
`(j, g)` is not the full level-`k` predicate (automatic for `j < k`). -/
theorem sigmaW_unfold_le {A : Semisentence (LXIn n) 1} {j k : Fin n} (hb : LevelBounded j A)
    (hjk : j.val ≤ k.val) {g : StageAt j.val} (hg : (⟨j, g⟩ : Stage n) ≠ Stage.top k)
    (t : Semiterm (LIinfN n) ξ m) :
    SigmaW k (unfold A j g t) ∧ SigmaW k (∼(unfold A j g t)) := by
  refine sigmaW_and_neg_of_forall_params (fun s hs => ?_)
  rcases params_unfold_of_levelBounded hb g t s hs with rfl | ⟨i, hi, rfl⟩
  · exact ⟨hjk, hg⟩
  · refine ⟨le_trans (le_of_lt hi) hjk, fun e => ?_⟩
    have := congrArg Fin.val (Stage.top_inj.mp e)
    exact absurd this (Nat.ne_of_lt (lt_of_lt_of_le hi hjk))

/-- A sequent extended by a `Σ(Ω_{k+1})` formula. -/
theorem sigmaW_cons {k : Fin n} {φ : Proposition (LIinfN n)} {Γ : Sequent (LIinfN n)}
    (hφ : SigmaW k φ) (hΓ : ∀ ψ ∈ Γ, SigmaW k ψ) : ∀ ψ ∈ φ :: Γ, SigmaW k ψ := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hφ
  · exact hΓ ψ hψ

end Sigma

/-! ### The formulas of rank exactly `Ω_{p+1}` -/

section RankOmega

variable {ξ : Type*} {m : ℕ}

theorem succ_ne_Omega (x : ThetaWNoteD) (p : ℕ) : ThetaWNoteD.succ x ≠ ThetaWNoteD.Omega p := by
  intro e
  rcases lt_or_ge x (ThetaWNoteD.Omega p) with h | h
  · exact absurd e (ne_of_lt (ThetaWNoteD.succ_lt_prin trivial h))
  · exact absurd e (ne_of_gt (lt_of_le_of_lt h (ThetaWNoteD.lt_succ x)))

/-- **The stage indices of atom rank exactly `Ω_{p+1}`**: the top of level `p`, or the stage
`0` of level `p + 1` (`rk(I_{p+1}^{≺0}) = Ω_{p+1} + ω·0`). -/
theorem atomRkStage_eq_Omega {s : Stage n} {p : ℕ}
    (h : atomRkStage s = ThetaWNoteD.Omega p) :
    (s.lvl.val = p ∧ s.val = ThetaWNoteD.Omega p) ∨
      (s.lvl.val = p + 1 ∧ s.val = ThetaWNoteD.zero) := by
  have hle : ThetaWNoteD.OmegaBelow s.lvl.val ≤ ThetaWNoteD.Omega p :=
    h ▸ ThetaWNoteD.le_add_right _ _
  rcases lt_trichotomy s.lvl.val p with hl | hl | hl
  · exfalso
    have h1 : atomRkStage s ≤ ThetaWNoteD.Omega s.lvl.val := by
      obtain ⟨j, a⟩ := s
      exact atomRkStage_mk_le_Omega j a
    have h2 := ThetaWNoteD.Omega_lt_Omega_iff.mpr hl
    rw [h] at h1
    exact absurd h1 (not_le_of_gt h2)
  · left
    refine ⟨hl, ?_⟩
    by_contra hne
    have hlt : s.val < ThetaWNoteD.Omega s.lvl.val := by
      rw [hl]; exact lt_of_le_of_ne (hl ▸ s.le) hne
    have hsne : s ≠ Stage.top s.lvl := fun e => by
      rw [e, Stage.val_top] at hlt; exact lt_irrefl _ hlt
    have h3 := (atomRkStage_lt_Omega_iff (k := s.lvl) (s := s)).mpr ⟨le_refl _, hsne⟩
    rw [h, ← hl] at h3
    exact lt_irrefl _ h3
  · rcases Nat.lt_or_ge (p + 1) s.lvl.val with hl2 | hl2
    · exfalso
      obtain ⟨q, hq⟩ : ∃ q, s.lvl.val = q + 1 := ⟨s.lvl.val - 1, by omega⟩
      rw [hq, ThetaWNoteD.OmegaBelow_succ] at hle
      have : p < q := by omega
      exact absurd hle (not_le_of_gt (ThetaWNoteD.Omega_lt_Omega_iff.mpr this))
    · right
      have hlv : s.lvl.val = p + 1 := by omega
      refine ⟨hlv, ?_⟩
      have e : ThetaWNoteD.OmegaBelow s.lvl.val + ThetaWNoteD.omegaMul s.val =
          ThetaWNoteD.Omega p := h
      rw [hlv, ThetaWNoteD.OmegaBelow_succ] at e
      by_contra hne
      have hpos : ThetaWNoteD.zero < s.val := lt_of_le_of_ne (ThetaWNoteD.zero_le' _) (Ne.symm hne)
      have h4 := ThetaWNoteD.add_lt_add_left (ThetaWNoteD.Omega p)
        (ThetaWNoteD.omegaMul_lt_omegaMul hpos)
      rw [ThetaWNoteD.omegaMul_zero, ThetaWNoteD.add_zero, e] at h4
      exact lt_irrefl _ h4

/-- **The formulas of rank exactly `Ω_{p+1}`**: `±I_p t`, or `±I_{p+1}^{≺0} t` (the empty
disjunction and its negation, whose rank `Ω_{p+1} + ω·0` coincides with the regular `Ω_{p+1}`
under the rank of `IDn/Rank.lean`; Buchholz's rank has no such coincidence). -/
theorem rk_eq_Omega_cases {p : ℕ} {φ : Semiformula (LIinfN n) ξ m}
    (h : rk φ = ThetaWNoteD.Omega p) :
    ∃ (s : Stage n) (t : Semiterm (LIinfN n) ξ m), (φ = stageAt s t ∨ φ = nstageAt s t) ∧
      ((s.lvl.val = p ∧ s.val = ThetaWNoteD.Omega p) ∨
        (s.lvl.val = p + 1 ∧ s.val = ThetaWNoteD.zero)) := by
  have hz : ThetaWNoteD.zero ≠ ThetaWNoteD.Omega p := ne_of_lt (ThetaWNoteD.zero_lt_Omega p)
  cases φ with
  | verum => exact absurd (rk_verum (ξ := ξ) (n := n) (m := m) ▸ h) hz
  | falsum => exact absurd (rk_falsum (ξ := ξ) (n := n) (m := m) ▸ h) hz
  | rel r v =>
    rw [rk_rel] at h
    rcases r with r | r
    · exact absurd h hz
    · cases r with
      | X => exact absurd h hz
      | stage s =>
        exact ⟨s, v 0, Or.inl (rel_eq_vec _ v), atomRkStage_eq_Omega h⟩
  | nrel r v =>
    rw [rk_nrel] at h
    rcases r with r | r
    · exact absurd h hz
    · cases r with
      | X => exact absurd h hz
      | stage s =>
        exact ⟨s, v 0, Or.inr (nrel_eq_vec _ v), atomRkStage_eq_Omega h⟩
  | and φ ψ => exact absurd ((rk_and φ ψ).symm.trans h) (succ_ne_Omega _ p)
  | or φ ψ => exact absurd ((rk_or φ ψ).symm.trans h) (succ_ne_Omega _ p)
  | all φ => exact absurd ((rk_all φ).symm.trans h) (succ_ne_Omega _ p)
  | exs φ => exact absurd ((rk_exs φ).symm.trans h) (succ_ne_Omega _ p)

end RankOmega

/-! ### Dropping the empty disjunction `I_j^{≺0} t` -/

section Drop

variable {A : Fin n → Semisentence (LXIn n) 1} {ρ : ThetaWNoteD}

/-- The positive stage of a positive stage atom, `none` for every other formula. -/
def posHeadStage {ξ : Type*} {m : ℕ} : Semiformula (LIinfN n) ξ m → Option (Stage n)
  | .rel r _ => relStage r
  | _ => none

theorem not_trueLit_stageAt (s : Stage n) (t : SyntacticTerm (LIinfN n)) :
    ¬ TrueLit (stageAt s t) := by
  rintro ⟨⟨j, r, v, (h | h), -⟩, -⟩
  · have := congrArg posHeadStage h
    exact nomatch this
  · exact nomatch h

/-- The claim of `drop_stage_zero` for a derivation of `Δ`. -/
def DropClaim (A : Fin n → Semisentence (LXIn n) 1) (ρ : ThetaWNoteD) (s : Stage n)
    (t : SyntacticTerm (LIinfN n)) (H : Set ThetaWNoteD → Set ThetaWNoteD) (α : ThetaWNoteD)
    (Δ : Sequent (LIinfN n)) : Prop :=
  ThetaWNoteD.IsOperator H → ∀ Γ : Sequent (LIinfN n), Δ ⊆ stageAt s t :: Γ →
    paramsVal Γ ⊆ H ∅ → IDnDerivable A ρ H α Γ

theorem drop_mem {s : Stage n} {t : SyntacticTerm (LIinfN n)} {θ : Proposition (LIinfN n)}
    {Δ Γ : Sequent (LIinfN n)} (hθ : θ ∈ Δ) (hΔ : Δ ⊆ stageAt s t :: Γ)
    (hne : θ ≠ stageAt s t) : θ ∈ Γ := by
  rcases List.mem_cons.mp (hΔ hθ) with h | h
  · exact absurd h hne
  · exact h

theorem drop_prem {s : Stage n} {t : SyntacticTerm (LIinfN n)} {φ : Proposition (LIinfN n)}
    {H : Set ThetaWNoteD → Set ThetaWNoteD} {α₀ : ThetaWNoteD} {Δ Γ : Sequent (LIinfN n)}
    (hH : ThetaWNoteD.IsOperator H) (d₀ : IDnDerivable A ρ H α₀ (φ :: Δ))
    (ih₀ : DropClaim A ρ s t H α₀ (φ :: Δ)) (hΔ : Δ ⊆ stageAt s t :: Γ)
    (hP : paramsVal Γ ⊆ H ∅) : IDnDerivable A ρ H α₀ (φ :: Γ) := by
  refine ih₀ hH (φ :: Γ) ?_ ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rcases List.mem_cons.mp (hΔ hx) with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  · rw [paramsVal_cons]
    exact Set.union_subset d₀.params_head_subset hP

theorem drop_aux {s : Stage n} (hs : s.val = ThetaWNoteD.zero) {t : SyntacticTerm (LIinfN n)}
    {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Δ : Sequent (LIinfN n)}
    (d : IDnDerivable A ρ H α Δ) : DropClaim A ρ s t H α Δ := by
  induction d with
  | literal hα _ hφ hm =>
    intro hH Γ hΔ hP
    exact .literal hα hP hφ (drop_mem hm hΔ fun h => not_trueLit_stageAt s t (h ▸ hφ))
  | verum hα _ hm =>
    intro hH Γ hΔ hP
    exact .verum hα hP (drop_mem hm hΔ fun h => nomatch h)
  | idX t' hα _ h1 h2 =>
    intro hH Γ hΔ hP
    refine .idX t' hα hP (drop_mem h1 hΔ fun h => ?_) (drop_mem h2 hΔ fun h => nomatch h)
    have := congrArg posHeadStage h
    exact nomatch this
  | and hα _ hm h0 h1 d0 d1 ih0 ih1 =>
    intro hH Γ hΔ hP
    exact .and hα hP (drop_mem hm hΔ fun h => nomatch h) h0 h1
      (drop_prem hH d0 ih0 hΔ hP) (drop_prem hH d1 ih1 hΔ hP)
  | orL hα _ hm h0 d0 ih0 =>
    intro hH Γ hΔ hP
    exact .orL hα hP (drop_mem hm hΔ fun h => nomatch h) h0 (drop_prem hH d0 ih0 hΔ hP)
  | orR hα _ hm h1 h0 d0 ih0 =>
    intro hH Γ hΔ hP
    exact .orR hα hP (drop_mem hm hΔ fun h => nomatch h) h1 h0 (drop_prem hH d0 ih0 hΔ hP)
  | all f hα _ hm hf d0 ih0 =>
    intro hH Γ hΔ hP
    exact .all f hα hP (drop_mem hm hΔ fun h => nomatch h) hf
      fun i => drop_prem hH (d0 i) (ih0 i) hΔ hP
  | exs i hα _ hm hn h0 d0 ih0 =>
    intro hH Γ hΔ hP
    exact .exs i hα hP (drop_mem hm hΔ fun h => nomatch h) hn h0 (drop_prem hH d0 ih0 hΔ hP)
  | @stage H' α' Δ' j a t' g α₀ hα _ hm hga hgα hgH h0 d0 ih0 =>
    intro hH Γ hΔ hP
    refine .stage g hα hP (drop_mem hm hΔ fun h => ?_) hga hgα hgH h0
      (drop_prem hH d0 ih0 hΔ hP)
    obtain ⟨e, -⟩ := stageAt_inj h
    have hv : a.1 = ThetaWNoteD.zero := by
      have := congrArg Stage.val e
      exact this.trans hs
    rw [hv] at hga
    exact absurd hga (not_lt_of_ge (ThetaWNoteD.zero_le' _))
  | @nstage H' α' Δ' j a t' f hα _ hm hf d0 ih0 =>
    intro hH Γ hΔ hP
    refine .nstage f hα hP (drop_mem hm hΔ fun h => nomatch h) hf fun g hg => ?_
    have hsub : H' ∅ ⊆ ThetaWNoteD.adjoin H' {g.1} ∅ := hH.mono (Set.empty_subset _)
    exact drop_prem (hH.adjoin {g.1}) (d0 g hg) (ih0 g hg) hΔ (hP.trans hsub)
  | @fix H' α' Δ' j t' α₀ hα _ hm hΩ h0 d0 ih0 =>
    intro hH Γ hΔ hP
    refine .fix hα hP (drop_mem hm hΔ fun h => ?_) hΩ h0 (drop_prem hH d0 ih0 hΔ hP)
    obtain ⟨e, -⟩ := stageAt_inj h
    have := congrArg Stage.val e
    rw [Stage.val_top, hs] at this
    exact absurd this (ne_of_gt (ThetaWNoteD.zero_lt_Omega _))
  | cut hα _ hr h0 d0 d1 ih0 ih1 =>
    intro hH Γ hΔ hP
    exact .cut hα hP hr h0 (drop_prem hH d0 ih0 hΔ hP) (drop_prem hH d1 ih1 hΔ hP)

/-- **The empty disjunction `I_j^{≺0} t` can be dropped**: `H ⊢^α_ρ Γ, I_j^{≺0} t` gives
`H ⊢^α_ρ Γ` (`I_j^{≺0} t ≃ ⋁_{γ ≺ 0}`, so it is never the principal formula of a clause). -/
theorem drop_stage_zero {s : Stage n} (hs : s.val = ThetaWNoteD.zero)
    {t : SyntacticTerm (LIinfN n)} {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD}
    {Γ : Sequent (LIinfN n)} (hH : ThetaWNoteD.IsOperator H)
    (d : IDnDerivable A ρ H α (stageAt s t :: Γ)) : IDnDerivable A ρ H α Γ := by
  refine drop_aux hs d hH Γ (List.Subset.refl _) ?_
  have h := d.params_subset
  rw [paramsVal_cons] at h
  exact Set.subset_union_right.trans h

end Drop

end Collapsing

end IDn

end OrdinalAnalysis
