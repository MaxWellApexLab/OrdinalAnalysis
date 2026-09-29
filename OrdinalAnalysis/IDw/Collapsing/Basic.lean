/-
  Vocabulary and small facts for the collapsing theorem of `ID_ω`
  (`IDw/Collapsing/Statement.lean`), all proved (no `sorry`).  Transcribed from
  `IDn/Collapsing/Basic.lean` (mechanical translation, then by hand); the new parts are the
  limit index `muBarW ⊤ = Ω_ω` (the design notes) and the `Jlev` arms.

  Source: W. Buchholz, *A simplified version of local predicativity*, in: P. Aczel,
  H. Simmons, S. Wainer (eds.), *Proof Theory* (Leeds 1990), CUP 1992, p. 26 (Lemma 4.6, the
  set `K̄ = {Ω̄_σ}` with `Ω̄_σ = Ω_σ + 1` for regular `Ω_σ`, `Ω_σ` otherwise, the hypothesis
  `𝒜(Θ; γ, κ, μ)`, Lemma 4.7 (𝒜1)–(𝒜4)); A. Freund, arXiv:2204.09321, Theorem 6.7 (one level).
  For `ID_ω`, `K̄` contains the singular `Ω_ω` with `Ω̄_ω = Ω_ω` (Buchholz p. 26: `Ω̄_σ = Ω_σ`
  for non-regular `Ω_σ`).

  Contents.

    `muBar m`                 `Ω̄_m`, `m : ℕ`: `0` for `m = 0`, `Ω_m + 1` (Lean `Omega (m-1) + 1`)
    `muBarW m`                `Ω̄_m`, `m : WithTop ℕ`: `muBar m` at `↑m`, `Ω_ω` at `⊤`
    `psi k`                   `ψ_κ`, `κ = Ω_{k+1}`: `ϑ_k` = `(Notn.thetaVLevel k).theta`
    `hat γ μ α`               `α̂ := γ + ω^{μ+μ+α}` (Buchholz 4.8's `γ + ω^{μ+α}`, doubled `μ`)
    `Hg γ X`                  `H_γ[Θ]` with `k(Θ) = X`: `adjoin (HopS γ) X`
    `capSeq k b Γ`            the level-`k` cap `Γ^b` of a sequent
    the (𝒜1)–(𝒜4) facts       `hat_mem`, `dom_hat`, `psi_hat_mem`, `lt_psi_hat`, … (any `m : WithTop ℕ`)
    `NiceS.rk_mem'`           `rk φ ∈ H(X)` for nice `H` (`Jlev` atoms have rank `Ω_ω` or `Ω_k + 1`);
                              declared in `IDw/CalculusAux.lean`
    `sigmaW_subst`            `Σ(Ω_{k+1})` is invariant under `φ ↦ φ/[t]`
    `sigmaW_mono`             `Σ(Ω_{k+1}) ⊆ Σ(Ω_{p+1})` for `k ≤ p`
    `sigmaW_unfold_le`        `A(j̄, t; I_j^{≺g}, Jlev j)`, `j ≤ k`, and its negation are `Σ(Ω_{k+1})`
    `sigmaW_unfold_top`       `A(k̄, t; I_k, Jlev k)` is `Σ(Ω_{k+1})` for `P`-positive `A`
    `le_of_lt_add_one_col`    `α ≺ β + 1 ⇒ α ⪯ β`
    `rk_eq_Omega_cases`       the formulas of rank `Ω_{p+1}`: `±I_p t`, `±I_{p+1}^{≺0} t`
    `drop_stage_zero`         the empty disjunction `I_j^{≺0} t` can be dropped from a sequent

  The limit facts (`ThetaVNoteD.exists_Omega_of_lt_OmegaW`, the `CollapsingLimit` window fact
  used by `CaseCut` at `m = ⊤`) come from `Ordinal/Collapsing/Limit.lean`.
-/
import OrdinalAnalysis.IDw.Calculus
import OrdinalAnalysis.Ordinal.Collapsing.ThetaVInstance
import OrdinalAnalysis.Ordinal.Collapsing.Limit

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaVTerm

/-- If `⟨xs⟩ ≺ ⟨ys, 0⟩` then not `⟨ys⟩ ≺ ⟨xs⟩` (ported from `ID1/ReductionAux.lean`). -/
theorem not_lt_of_lt_append_zero_col : ∀ (ys xs : List ThetaVTerm),
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

end ThetaVTerm

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

/-! ### Ordinal vocabulary -/

/-- `α ≺ β + 1` gives `α ⪯ β`. -/
theorem le_of_lt_add_one_col {a b : ThetaVNoteD} (h : a < b + ThetaVNoteD.one) : a ≤ b := by
  rw [ThetaVNoteD.add_one_eq_succ] at h
  refine le_of_not_gt fun hba => ?_
  rw [ThetaVNoteD.lt_iff_entries, ThetaVNoteD.succ, ThetaVNoteD.entries_nadd_one] at h
  exact ThetaVTerm.not_lt_of_lt_append_zero_col _ _ h (ThetaVNoteD.lt_iff_entries.mp hba)

/-- **`Ω̄_m`, `m : ℕ`** (Buchholz p. 26, `K̄ = {Ω̄_σ}`), for the regulars `Ω_1, Ω_2, …` of
`ThetaVNoteD` and `Ω_0 := 0` (not regular): `Ω̄_0 = 0`, `Ω̄_m = Ω_m + 1` for `m ≥ 1`.  Lean's
`Omega s` is `Ω_{s+1}`, so `muBar (s+1) = Omega s + 1`.  (`IDn`'s `muBar`, verbatim.) -/
def muBar : ℕ → ThetaVNoteD
  | 0 => ThetaVNoteD.zero
  | s + 1 => ThetaVNoteD.Omega s + ThetaVNoteD.one

@[simp] theorem muBar_zero : muBar 0 = ThetaVNoteD.zero := rfl

@[simp] theorem muBar_succ (s : ℕ) : muBar (s + 1) = ThetaVNoteD.Omega s + ThetaVNoteD.one := rfl

/-- **`Ω̄_m`, `m : WithTop ℕ`** (design §3.3): `↑0 ↦ 0`, `↑(s+1) ↦ Ω_{s+1} + 1`, `⊤ ↦ Ω_ω`.
`Ω_ω` is singular, so `Ω̄_ω = Ω_ω` (Buchholz p. 26). The main induction of Theorem 4.8 runs
over `m : WithTop ℕ` (well founded: `WithTop.wellFoundedLT`). -/
def muBarW : WithTop ℕ → ThetaVNoteD
  | ⊤ => ThetaVNoteD.OmegaW
  | (m : ℕ) => muBar m

@[simp] theorem muBarW_top : muBarW ⊤ = ThetaVNoteD.OmegaW := rfl

@[simp] theorem muBarW_coe (m : ℕ) : muBarW (m : WithTop ℕ) = muBar m := rfl

/-- **`ψ_κ` at `κ = Ω_{k+1}`**: the collapsing function `ϑ_k` of the merged interface
(`Notn.thetaVLevel k`, total, junk `0` outside its domain `DomK k`). -/
noncomputable def psi (k : ℕ) (a : ThetaVNoteD) : ThetaVNoteD := (Notn.thetaVLevel k).theta a

/-- **`α̂ := γ + ω^{μ+μ+α}`**: Buchholz's Theorem 4.8 has `γ + ω^{μ+α}`.  The exponent carries
`μ` twice so that in the step (□) the base `γ' ⪰ ω^{μ+μ} ⪰ ω^{Ω_{σ+1}·2}` exceeds every argument
`Ω_{σ+1}·ρ + β` (`ρ, β ≺ Ω_{σ+1}`) of the syntactic Veblen function `φ_σ(ρ, β) = ϑ_σ(Ω_{σ+1}·ρ + β)`:
`HopS` is closed under `ϑ_σ` only on arguments `⪯ γ'` (`theta_mem_HopS`), unlike Buchholz's `H_γ`,
which is closed under `φ` by definition (Lemma 4.6 b)).  Unchanged from `IDn`. -/
def hat (γ μ α : ThetaVNoteD) : ThetaVNoteD := γ + ThetaVNoteD.omegaPow (μ + μ + α)

/-- **`H_γ[Θ]`**, `k(Θ) = X`: the level-free Buchholz operator `H_γ` (`HopS γ`) with `X`
adjoined. -/
def Hg (γ : ThetaVNoteD) (X : Set ThetaVNoteD) : Set ThetaVNoteD → Set ThetaVNoteD :=
  ThetaVNoteD.adjoin (ThetaVNoteD.HopS γ) X

/-- **The level-`k` cap of a sequent**, `Γ^b` (Freund's `Γ^β`, Buchholz's `Γ^β`, at level
`k`): every `I_k^{≺Ω_{k+1}}` replaced by `I_k^{≺b}`. -/
def capSeq (k : ℕ) (b : StageAt k) (Γ : Sequent LIinfW) : Sequent LIinfW :=
  Γ.map (capAt k b)

@[simp] theorem capSeq_singleton (k : ℕ) (b : StageAt k) (φ : Proposition LIinfW) :
    capSeq k b [φ] = [capAt k b φ] := rfl

/-! ### The operator `H_γ[Θ]` -/

theorem Hg_empty (γ : ThetaVNoteD) (X : Set ThetaVNoteD) :
    Hg γ X ∅ = ThetaVNoteD.HopS γ X := by
  simp [Hg, ThetaVNoteD.adjoin]

theorem Hg_niceS (γ : ThetaVNoteD) (X : Set ThetaVNoteD) : ThetaVNoteD.NiceS (Hg γ X) :=
  (ThetaVNoteD.HopS_nice γ).adjoin X

theorem Hg_isOperator (γ : ThetaVNoteD) (X : Set ThetaVNoteD) : ThetaVNoteD.IsOperator (Hg γ X) :=
  (Hg_niceS γ X).1

theorem Hg_mono {γ γ' : ThetaVNoteD} (h : γ ≤ γ') (X : Set ThetaVNoteD) :
    ∀ Z, Hg γ X Z ⊆ Hg γ' X Z :=
  fun _ => ThetaVNoteD.HopS_subset_HopS_of_le h _

theorem Hg_adjoin (γ : ThetaVNoteD) (X Z : Set ThetaVNoteD) :
    ThetaVNoteD.adjoin (Hg γ X) Z = Hg γ (X ∪ Z) := by
  funext Y
  simp only [Hg, ThetaVNoteD.adjoin, Set.union_assoc]

theorem mem_Hg_empty {γ x : ThetaVNoteD} {X : Set ThetaVNoteD} :
    x ∈ Hg γ X ∅ ↔ x ∈ ThetaVNoteD.HopS γ X := by rw [Hg_empty]

/-! ### The limit `Ω_ω` -/

/-- `Ω̄_m ≺ Ω_ω` for finite `m`. -/
theorem muBar_lt_OmegaW (m : ℕ) : muBar m < ThetaVNoteD.OmegaW := by
  cases m with
  | zero => exact ThetaVNoteD.zero_lt_OmegaW
  | succ s =>
    rw [muBar_succ, ThetaVNoteD.add_one_eq_succ]
    exact ThetaVNoteD.succ_lt_prin ThetaVTerm.isPrin_OmegaW (ThetaVNoteD.Omega_lt_OmegaW s)

/-- `Ω̄_m ⪯ Ω_ω` for every `m : WithTop ℕ`. -/
theorem muBarW_le_OmegaW (m : WithTop ℕ) : muBarW m ≤ ThetaVNoteD.OmegaW := by
  induction m using WithTop.recTopCoe with
  | top => exact le_rfl
  | coe m => exact le_of_lt (muBar_lt_OmegaW m)

-- `NiceS.rk_mem'` (Freund, Exercise 5.5 (e), formula half) lives in `IDw/CalculusAux.lean`.

/-! ### Membership, domain and comparison facts (Buchholz, Lemma 4.7 (𝒜1)–(𝒜4))

Stated for every `m : WithTop ℕ` (the case lemmas are uniform in `m`); only `muBarW_mem` looks
at `m`. The finite-`m` order facts (`muBar_mono`, `muBar_lt_Omega`, `Omega_le_muBar`) are
`IDn`'s, on `muBar`. -/

section Facts

variable {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD}

theorem muBar_mem (m : ℕ) (a : ThetaVNoteD) : muBar m ∈ ThetaVNoteD.HopS a X := by
  cases m with
  | zero => exact (ThetaVNoteD.HopS_nice a).zero_mem
  | succ s =>
    exact (ThetaVNoteD.HopS_nice a).add_mem ((ThetaVNoteD.HopS_nice a).Omega_mem s)
      (ThetaVNoteD.HopS_nice a).one_mem

theorem muBarW_mem (m : WithTop ℕ) (a : ThetaVNoteD) : muBarW m ∈ ThetaVNoteD.HopS a X := by
  induction m using WithTop.recTopCoe with
  | top => exact (ThetaVNoteD.HopS_nice a).OmegaW_mem
  | coe m => exact muBar_mem m a

theorem muBar_mono {a b : ℕ} (h : a ≤ b) : muBar a ≤ muBar b := by
  cases a with
  | zero => exact ThetaVNoteD.zero_le' _
  | succ a =>
    cases b with
    | zero => exact absurd h (Nat.not_succ_le_zero a)
    | succ b =>
      rw [muBar_succ, muBar_succ, ThetaVNoteD.add_one_eq_succ, ThetaVNoteD.add_one_eq_succ]
      refine ThetaVNoteD.succ_le_succ ?_
      rcases Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ h) with h' | rfl
      · exact le_of_lt (ThetaVNoteD.Omega_lt_Omega_iff.mpr h')
      · exact le_rfl

/-- `Ω̄_p ≺ Ω_{p+1}` (Lean `Omega p`). -/
theorem muBar_lt_Omega (p : ℕ) : muBar p < ThetaVNoteD.Omega p := by
  cases p with
  | zero => exact ThetaVNoteD.zero_lt_Omega 0
  | succ s =>
    rw [muBar_succ, ThetaVNoteD.add_one_eq_succ]
    exact ThetaVNoteD.succ_lt_prin trivial (ThetaVNoteD.Omega_lt_Omega_iff.mpr (Nat.lt_succ_self s))

/-- `Ω_{p+1} ⪯ Ω̄_m` for `p < m`: a regular `π ≺ μ`. -/
theorem Omega_le_muBar {p m : ℕ} (h : p < m) : ThetaVNoteD.Omega p ≤ muBar m := by
  cases m with
  | zero => exact absurd h (Nat.not_lt_zero p)
  | succ m =>
    rw [muBar_succ]
    refine le_trans ?_ (ThetaVNoteD.le_add_right _ _)
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | rfl
    · exact le_of_lt (ThetaVNoteD.Omega_lt_Omega_iff.mpr h')
    · exact le_rfl

theorem hat_lt_hat (γ μ : ThetaVNoteD) {α₀ α : ThetaVNoteD} (h : α₀ < α) :
    hat γ μ α₀ < hat γ μ α :=
  ThetaVNoteD.add_lt_add_left γ
    (ThetaVNoteD.omegaPow_lt_omegaPow (ThetaVNoteD.add_lt_add_left (μ + μ) h))

theorem gamma_lt_hat (γ μ α : ThetaVNoteD) : γ < hat γ μ α :=
  ThetaVNoteD.lt_add_omegaPow_hull γ (μ + μ + α)

theorem gamma_le_hat (γ μ α : ThetaVNoteD) : γ ≤ hat γ μ α := le_of_lt (gamma_lt_hat γ μ α)

/-- The exponent `μ + μ + α` lies in `H_γ[Θ]`. -/
theorem exp_mem {m : WithTop ℕ} {α : ThetaVNoteD} (hα : α ∈ ThetaVNoteD.HopS γ X) :
    muBarW m + muBarW m + α ∈ ThetaVNoteD.HopS γ X :=
  (ThetaVNoteD.HopS_nice γ).add_mem
    ((ThetaVNoteD.HopS_nice γ).add_mem (muBarW_mem m γ) (muBarW_mem m γ)) hα

/-- (𝒜1), first half: `α̂ ∈ H_{α̂}[Θ]`. -/
theorem hat_mem {m : WithTop ℕ} {α : ThetaVNoteD} (hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (hα : α ∈ ThetaVNoteD.HopS γ X) :
    hat γ (muBarW m) α ∈ ThetaVNoteD.HopS (hat γ (muBarW m) α) X :=
  ThetaVNoteD.add_omegaPow_mem_HopS hγ (exp_mem hα)

/-- `α̂ ∈ H_γ[Θ]`. -/
theorem hat_mem_self {m : WithTop ℕ} {α : ThetaVNoteD} (hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (hα : α ∈ ThetaVNoteD.HopS γ X) : hat γ (muBarW m) α ∈ ThetaVNoteD.HopS γ X :=
  (ThetaVNoteD.HopS_nice γ).add_mem hγ ((ThetaVNoteD.HopS_nice γ).omegaPow_mem (exp_mem hα))

/-- The domain side condition of `ϑ_k` at `α̂` (`HullDom.dom_add_omegaPow`, through the
interface field `dom_add_omegaPow`; at `m = ⊤` the exponent contains `Ω_ω`). -/
theorem dom_hat {m : WithTop ℕ} {α : ThetaVNoteD} (hX : ThetaVNoteD.HullHypGe k γ X)
    (hγ : γ ∈ ThetaVNoteD.HopS γ X) (hα : α ∈ ThetaVNoteD.HopS γ X) :
    (Notn.thetaVLevel k).D (hat γ (muBarW m) α) :=
  (Notn.thetaVLevel k).dom_add_omegaPow (a := γ) (b := muBarW m + muBarW m + α) hX hγ
    (exp_mem hα)

/-- (𝒜1), second half: `ψ_κ α̂ ∈ H_{α̂}[Θ]` (Buchholz's (1) in the proof of Theorem 4.8). -/
theorem psi_hat_mem {m : WithTop ℕ} {α : ThetaVNoteD} (hX : ThetaVNoteD.HullHypGe k γ X)
    (hγ : γ ∈ ThetaVNoteD.HopS γ X) (hα : α ∈ ThetaVNoteD.HopS γ X) :
    psi k (hat γ (muBarW m) α) ∈ ThetaVNoteD.HopS (hat γ (muBarW m) α) X :=
  (Notn.thetaVLevel k).theta_add_omegaPow_mem_Hop (a := γ) (b := muBarW m + muBarW m + α) hX hγ
    (exp_mem hα)

theorem psi_lt_Omega (k : ℕ) (a : ThetaVNoteD) : psi k a < ThetaVNoteD.Omega k :=
  (Notn.thetaVLevel k).theta_lt_Omega a

/-- (𝒜3): `H_γ[Θ] ∩ Ω_{k+1} ⊆ ψ_k(α̂)`. -/
theorem lt_psi_hat {m : WithTop ℕ} {α d : ThetaVNoteD} (hX : ThetaVNoteD.HullHypGe k γ X)
    (hγ : γ ∈ ThetaVNoteD.HopS γ X) (hα : α ∈ ThetaVNoteD.HopS γ X)
    (hd : d ∈ ThetaVNoteD.HopS γ X) (hdΩ : d < ThetaVNoteD.Omega k) :
    d < psi k (hat γ (muBarW m) α) :=
  (Notn.thetaVLevel k).hullHyp_lt_theta hX (gamma_lt_hat γ _ α) (dom_hat hX hγ hα) hd hdΩ

/-- Buchholz's (2) in the proof of Theorem 4.8 (from (𝒜2)): `α₀ ≺ α`, `α₀ ∈ H_γ[Θ]` give
`ψ_κ α̂₀ ≺ ψ_κ α̂`. -/
theorem psi_hat_lt_psi_hat {m : WithTop ℕ} {α₀ α : ThetaVNoteD}
    (hX : ThetaVNoteD.HullHypGe k γ X)
    (hγ : γ ∈ ThetaVNoteD.HopS γ X) (hα₀ : α₀ ∈ ThetaVNoteD.HopS γ X)
    (hα : α ∈ ThetaVNoteD.HopS γ X) (h : α₀ < α) :
    psi k (hat γ (muBarW m) α₀) < psi k (hat γ (muBarW m) α) :=
  (Notn.thetaVLevel k).theta_lt_theta_add (a := γ) (b := muBarW m + muBarW m + α)
    (b' := muBarW m + muBarW m + α₀) hX hγ
    (exp_mem hα) (exp_mem hα₀) (ThetaVNoteD.add_lt_add_left _ h)

/-- A general comparison: `γ ⪯ x ≺ y`, `x ∈ H_γ[Θ]`, both in the domain, give
`ψ_k x ≺ ψ_k y` (Freund, Proposition 3.11 (c), through the interface). -/
theorem psi_lt_psi {x y : ThetaVNoteD} (hX : ThetaVNoteD.HullHypGe k γ X) (hγx : γ ≤ x)
    (hxy : x < y) (hx : x ∈ ThetaVNoteD.HopS γ X) (hDx : (Notn.thetaVLevel k).D x)
    (hDy : (Notn.thetaVLevel k).D y) : psi k x < psi k y :=
  (Notn.thetaVLevel k).theta_lt_theta_of_mem_Hop hX hγx hxy hx hDx hDy

/-- `ψ_k` of a domain point is principal, hence positive, and above `Ω_k` (Lean
`OmegaBelow k`). -/
theorem OmegaBelow_lt_psi {a : ThetaVNoteD} (hD : (Notn.thetaVLevel k).D a) :
    ThetaVNoteD.OmegaBelow k < psi k a := by
  cases k with
  | zero =>
    have hp : ThetaVTerm.IsPrin (psi 0 a).1 := (Notn.thetaVLevel 0).isPrin_theta hD
    exact lt_trans ThetaVNoteD.zero_lt_one (ThetaVNoteD.one_lt_prin hp)
  | succ s => exact Notn.thetaVTower.Omega_lt_theta_succ s a hD

theorem Omega_le_psi {j : ℕ} (hjk : j < k) {a : ThetaVNoteD} (hD : (Notn.thetaVLevel k).D a) :
    ThetaVNoteD.Omega j ≤ psi k a :=
  le_trans (ThetaVNoteD.Omega_le_OmegaBelow_of_lt hjk) (le_of_lt (OmegaBelow_lt_psi hD))

end Facts

/-! ### `Σ(Ω_{k+1})` -/

section Sigma

variable {ξ : Type*} {m : ℕ}

/-- `Σ(Ω_{k+1})` is invariant under a one-variable substitution (`IDn.sigmaW_subst`; `IDw/Language`
has only the two-variable `sigmaW_subst2`). -/
@[simp] theorem sigmaW_subst (k : ℕ) (φ : Semiformula LIinfW ξ 1) (t : Semiterm LIinfW ξ m) :
    SigmaW k (φ/[t]) ↔ SigmaW k φ := sigmaW_rew k _ φ

/-- **`Σ(Ω_{k+1}) ⊆ Σ(Ω_{p+1})` for `k ≤ p`.** -/
theorem sigmaW_mono {k p : ℕ} (hkp : k ≤ p) {φ : Semiformula LIinfW ξ m}
    (h : SigmaW k φ) : SigmaW p φ := by
  induction φ using Semiformula.rec' with
  | hverum => trivial
  | hfalsum => trivial
  | hrel r v =>
    rcases r with r | r
    · trivial
    · cases r with
      | X => trivial
      | stage s => exact le_trans (h : s.lvl ≤ k) hkp
      | jlev ℓ =>
        exact le_trans (h : ℓ ≤ (k : WithTop ℕ)) (WithTop.coe_le_coe.mpr hkp)
  | hnrel r v =>
    rcases r with r | r
    · trivial
    · cases r with
      | X => trivial
      | stage s =>
        obtain ⟨h1, h2⟩ := (h : s.lvl ≤ k ∧ s ≠ Stage.top k)
        refine ⟨le_trans h1 hkp, fun e => h2 ?_⟩
        have hl : s.lvl = p := by rw [e, Stage.lvl_top]
        have hpk : p = k := le_antisymm (hl ▸ h1) hkp
        rw [e, hpk]
      | jlev ℓ =>
        exact le_trans (h : ℓ ≤ (k : WithTop ℕ)) (WithTop.coe_le_coe.mpr hkp)
  | hand φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | hor φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | hall φ ih => exact ih h
  | hexs φ ih => exact ih h

theorem sigmaW_mono_seq {k p : ℕ} (hkp : k ≤ p) {Γ : Sequent LIinfW}
    (h : ∀ φ ∈ Γ, SigmaW k φ) : ∀ φ ∈ Γ, SigmaW p φ :=
  fun φ hφ => sigmaW_mono hkp (h φ hφ)

/-- The compiled schema at level `j`, bound `g`, lies in `Σ(Ω_{k+1})` for `j ≤ k` unless
`(j, g)` is the full level-`k` predicate (both polarities: `P ↦ I_j^{≺g}`, `Q ↦ Jlev j`). -/
theorem sigmaW_lMap_formHomAt_le {j k : ℕ} (hjk : j ≤ k) {g : StageAt j}
    (hg : (⟨j, g⟩ : Stage) ≠ Stage.top k) :
    ∀ {n : ℕ} (B : Semiformula LForm Empty n), SigmaW k (Semiformula.lMap (formHomAt j g) B) := by
  intro n B
  induction B using Semiformula.rec' with
  | hverum => trivial
  | hfalsum => trivial
  | hrel r v =>
    show RelSigmaW k (formRelAt j g r)
    rcases r with r | r
    · trivial
    · cases r with
      | P => exact hjk
      | Q => exact WithTop.coe_le_coe.mpr hjk
  | hnrel r v =>
    show NrelSigmaW k (formRelAt j g r)
    rcases r with r | r
    · trivial
    · cases r with
      | P => exact ⟨hjk, hg⟩
      | Q => exact WithTop.coe_le_coe.mpr hjk
  | hand φ ψ ihφ ihψ => rw [LogicalConnective.HomClass.map_and]; exact ⟨ihφ, ihψ⟩
  | hor φ ψ ihφ ihψ => rw [LogicalConnective.HomClass.map_or]; exact ⟨ihφ, ihψ⟩
  | hall φ ih => rw [Semiformula.lMap_all]; exact ih
  | hexs φ ih => rw [Semiformula.lMap_exs]; exact ih

/-- **`A(j̄, t; I_j^{≺g}, Jlev j)` and its negation are `Σ(Ω_{k+1})`** for `j ≤ k`, provided the
stage `(j, g)` is not the full level-`k` predicate (automatic for `j < k`).  `IDn`'s
`sigmaW_unfold_le` without its `LevelBounded` hypothesis (automatic in `ID_ω`: `Q ↦ Jlev j`),
and with the schema `A` explicit (it is no longer determined by that hypothesis). -/
theorem sigmaW_unfold_le (A : FormJ) {j k : ℕ} (hjk : j ≤ k) {g : StageAt j}
    (hg : (⟨j, g⟩ : Stage) ≠ Stage.top k) (t : Semiterm LIinfW ξ m) :
    SigmaW k (unfoldW A j g t) ∧ SigmaW k (∼(unfoldW A j g t)) := by
  have hneg : ∼(unfoldW A j g t) = unfoldW (∼A) j g t := by simp [unfoldW, formAtW]
  refine ⟨?_, ?_⟩
  · have key := sigmaW_lMap_formHomAt_le hjk hg A
    unfold unfoldW formAtW
    rwa [sigmaW_subst2, sigmaW_rew]
  · rw [hneg]
    have key := sigmaW_lMap_formHomAt_le hjk hg (∼A)
    unfold unfoldW formAtW
    rwa [sigmaW_subst2, sigmaW_rew]

/-- The compiled schema at the top of level `k` lies in `Σ(Ω_{k+1})` when `P` occurs only
positively (`Q ↦ Jlev k` is allowed in both polarities). -/
theorem sigmaW_lMap_formHomAt_top {k : ℕ} :
    ∀ {n : ℕ} (B : Semiformula LForm Empty n), PositiveP B →
      SigmaW k (Semiformula.lMap (formHomAt k (StageAt.top k)) B) := by
  intro n B
  induction B using Semiformula.rec' with
  | hverum => intro _; trivial
  | hfalsum => intro _; trivial
  | hrel r v =>
    intro _
    show RelSigmaW k (formRelAt k (StageAt.top k) r)
    rcases r with r | r
    · trivial
    · cases r with
      | P => exact le_refl k
      | Q => exact le_refl (k : WithTop ℕ)
  | hnrel r v =>
    intro hp
    show NrelSigmaW k (formRelAt k (StageAt.top k) r)
    rcases r with r | r
    · trivial
    · cases r with
      | P => exact (hp : False).elim
      | Q => exact le_refl (k : WithTop ℕ)
  | hand φ ψ ihφ ihψ =>
    intro hp; rw [LogicalConnective.HomClass.map_and]; exact ⟨ihφ hp.1, ihψ hp.2⟩
  | hor φ ψ ihφ ihψ =>
    intro hp; rw [LogicalConnective.HomClass.map_or]; exact ⟨ihφ hp.1, ihψ hp.2⟩
  | hall φ ih => intro hp; rw [Semiformula.lMap_all]; exact ih hp
  | hexs φ ih => intro hp; rw [Semiformula.lMap_exs]; exact ih hp

/-- **`A(k̄, t; I_k, Jlev k)` is `Σ(Ω_{k+1})`** when `A` is positive in `P` (`IDn`'s
`sigmaW_unfold_top`, without its `LevelBounded` hypothesis; `A` explicit). -/
theorem sigmaW_unfold_top (A : FormJ) (hp : PositiveP A) {k : ℕ} (t : Semiterm LIinfW ξ m) :
    SigmaW k (unfoldW A k (StageAt.top k) t) := by
  have key := sigmaW_lMap_formHomAt_top (k := k) A hp
  unfold unfoldW formAtW
  rwa [sigmaW_subst2, sigmaW_rew]

/-- A sequent extended by a `Σ(Ω_{k+1})` formula. -/
theorem sigmaW_cons {k : ℕ} {φ : Proposition LIinfW} {Γ : Sequent LIinfW}
    (hφ : SigmaW k φ) (hΓ : ∀ ψ ∈ Γ, SigmaW k ψ) : ∀ ψ ∈ φ :: Γ, SigmaW k ψ := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hφ
  · exact hΓ ψ hψ

end Sigma

/-! ### The formulas of rank exactly `Ω_{p+1}` -/

section RankOmega

variable {ξ : Type*} {m : ℕ}

theorem succ_ne_Omega (x : ThetaVNoteD) (p : ℕ) : ThetaVNoteD.succ x ≠ ThetaVNoteD.Omega p := by
  intro e
  rcases lt_or_ge x (ThetaVNoteD.Omega p) with h | h
  · exact absurd e (ne_of_lt (ThetaVNoteD.succ_lt_prin trivial h))
  · exact absurd e (ne_of_gt (lt_of_le_of_lt h (ThetaVNoteD.lt_succ x)))

/-- A unary negated atom is `r ![v 0]` (the `nrel` twin of `IDw.rel_eq_vec`). -/
theorem nrel_eq_vec {k : ℕ} (r : LIinfW.Rel 1) (v : Fin 1 → Semiterm LIinfW ξ k) :
    Semiformula.nrel r v = Semiformula.nrel r ![v 0] := by
  congr 1; funext i; obtain rfl := Subsingleton.elim i 0; rfl

/-- No `Jlev` atom has a regular rank: `Ω_ω` and `Ω_k + 1` are never `Ω_{p+1}`. -/
theorem atomRkJlev_ne_Omega (ℓ : WithTop ℕ) (p : ℕ) : atomRkJlev ℓ ≠ ThetaVNoteD.Omega p := by
  induction ℓ using WithTop.recTopCoe with
  | top => exact ne_of_gt (ThetaVNoteD.Omega_lt_OmegaW p)
  | coe k => exact succ_ne_Omega _ p

/-- **The stage indices of atom rank exactly `Ω_{p+1}`**: the top of level `p`, or the stage
`0` of level `p + 1` (`rk(I_{p+1}^{≺0}) = Ω_{p+1} + ω·0`). -/
theorem atomRkStage_eq_Omega {s : Stage} {p : ℕ}
    (h : atomRkStage s = ThetaVNoteD.Omega p) :
    (s.lvl = p ∧ s.val = ThetaVNoteD.Omega p) ∨
      (s.lvl = p + 1 ∧ s.val = ThetaVNoteD.zero) := by
  have hle : ThetaVNoteD.OmegaBelow s.lvl ≤ ThetaVNoteD.Omega p :=
    h ▸ ThetaVNoteD.le_add_right _ _
  rcases lt_trichotomy s.lvl p with hl | hl | hl
  · exfalso
    have h1 : atomRkStage s ≤ ThetaVNoteD.Omega s.lvl := by
      obtain ⟨j, a⟩ := s
      exact atomRkStage_mk_le_Omega j a
    have h2 := ThetaVNoteD.Omega_lt_Omega_iff.mpr hl
    rw [h] at h1
    exact absurd h1 (not_le_of_gt h2)
  · left
    refine ⟨hl, ?_⟩
    by_contra hne
    have hlt : s.val < ThetaVNoteD.Omega s.lvl := by
      rw [hl]; exact lt_of_le_of_ne (hl ▸ s.le) hne
    have hsne : s ≠ Stage.top s.lvl := fun e => by
      rw [e, Stage.val_top] at hlt; exact lt_irrefl _ hlt
    have h3 := (atomRkStage_lt_Omega_iff (k := s.lvl) (s := s)).mpr ⟨le_refl _, hsne⟩
    rw [h, ← hl] at h3
    exact lt_irrefl _ h3
  · rcases Nat.lt_or_ge (p + 1) s.lvl with hl2 | hl2
    · exfalso
      obtain ⟨q, hq⟩ : ∃ q, s.lvl = q + 1 := ⟨s.lvl - 1, by omega⟩
      rw [hq, ThetaVNoteD.OmegaBelow_succ] at hle
      have : p < q := by omega
      exact absurd hle (not_le_of_gt (ThetaVNoteD.Omega_lt_Omega_iff.mpr this))
    · right
      have hlv : s.lvl = p + 1 := by omega
      refine ⟨hlv, ?_⟩
      have e : ThetaVNoteD.OmegaBelow s.lvl + ThetaVNoteD.omegaMul s.val =
          ThetaVNoteD.Omega p := h
      rw [hlv, ThetaVNoteD.OmegaBelow_succ] at e
      by_contra hne
      have hpos : ThetaVNoteD.zero < s.val := lt_of_le_of_ne (ThetaVNoteD.zero_le' _) (Ne.symm hne)
      have h4 := ThetaVNoteD.add_lt_add_left (ThetaVNoteD.Omega p)
        (ThetaVNoteD.omegaMul_lt_omegaMul hpos)
      rw [ThetaVNoteD.omegaMul_zero, ThetaVNoteD.add_zero, e] at h4
      exact lt_irrefl _ h4

/-- **The formulas of rank exactly `Ω_{p+1}`**: `±I_p t`, or `±I_{p+1}^{≺0} t` (the empty
disjunction and its negation, whose rank `Ω_{p+1} + ω·0` coincides with the regular `Ω_{p+1}`
under the rank of `IDw/Rank.lean`; Buchholz's rank has no such coincidence).  No `Jlev` atom
(`atomRkJlev_ne_Omega`). -/
theorem rk_eq_Omega_cases {p : ℕ} {φ : Semiformula LIinfW ξ m}
    (h : rk φ = ThetaVNoteD.Omega p) :
    ∃ (s : Stage) (t : Semiterm LIinfW ξ m), (φ = stageAt s t ∨ φ = nstageAt s t) ∧
      ((s.lvl = p ∧ s.val = ThetaVNoteD.Omega p) ∨
        (s.lvl = p + 1 ∧ s.val = ThetaVNoteD.zero)) := by
  have hz : ThetaVNoteD.zero ≠ ThetaVNoteD.Omega p := ne_of_lt (ThetaVNoteD.zero_lt_Omega p)
  cases φ with
  | verum => exact absurd (rk_verum (ξ := ξ) (m := m) ▸ h) hz
  | falsum => exact absurd (rk_falsum (ξ := ξ) (m := m) ▸ h) hz
  | rel r v =>
    rw [rk_rel] at h
    rcases r with r | r
    · exact absurd h hz
    · cases r with
      | X => exact absurd h hz
      | stage s =>
        exact ⟨s, v 0, Or.inl (rel_eq_vec _ v), atomRkStage_eq_Omega h⟩
      | jlev ℓ => exact absurd h (atomRkJlev_ne_Omega ℓ p)
  | nrel r v =>
    rw [rk_nrel] at h
    rcases r with r | r
    · exact absurd h hz
    · cases r with
      | X => exact absurd h hz
      | stage s =>
        exact ⟨s, v 0, Or.inr (nrel_eq_vec _ v), atomRkStage_eq_Omega h⟩
      | jlev ℓ => exact absurd h (atomRkJlev_ne_Omega ℓ p)
  | and φ ψ => exact absurd ((rk_and φ ψ).symm.trans h) (succ_ne_Omega _ p)
  | or φ ψ => exact absurd ((rk_or φ ψ).symm.trans h) (succ_ne_Omega _ p)
  | all φ => exact absurd ((rk_all φ).symm.trans h) (succ_ne_Omega _ p)
  | exs φ => exact absurd ((rk_exs φ).symm.trans h) (succ_ne_Omega _ p)

end RankOmega

/-! ### Dropping the empty disjunction `I_j^{≺0} t` -/

section Drop

variable {A : FormJ} {ρ : ThetaVNoteD}

/-- The positive stage of a positive stage atom, `none` for every other formula (including
every `Jlev ℓ (s,t)`). -/
def posHeadStage {ξ : Type*} {m : ℕ} : Semiformula LIinfW ξ m → Option Stage
  | .rel r _ => relStage r
  | _ => none

theorem not_trueLit_stageAt (s : Stage) (t : SyntacticTerm LIinfW) :
    ¬ TrueLit (stageAt s t) := by
  rintro ⟨⟨j, r, v, (h | h), -⟩, -⟩
  · have := congrArg posHeadStage h
    exact nomatch this
  · exact nomatch h

/-- The claim of `drop_stage_zero` for a derivation of `Δ`. -/
def DropClaim (A : FormJ) (ρ : ThetaVNoteD) (s : Stage)
    (t : SyntacticTerm LIinfW) (H : Set ThetaVNoteD → Set ThetaVNoteD) (α : ThetaVNoteD)
    (Δ : Sequent LIinfW) : Prop :=
  ThetaVNoteD.IsOperator H → ∀ Γ : Sequent LIinfW, Δ ⊆ stageAt s t :: Γ →
    paramsVal Γ ⊆ H ∅ → IDwDerivable A ρ H α Γ

theorem drop_mem {s : Stage} {t : SyntacticTerm LIinfW} {θ : Proposition LIinfW}
    {Δ Γ : Sequent LIinfW} (hθ : θ ∈ Δ) (hΔ : Δ ⊆ stageAt s t :: Γ)
    (hne : θ ≠ stageAt s t) : θ ∈ Γ := by
  rcases List.mem_cons.mp (hΔ hθ) with h | h
  · exact absurd h hne
  · exact h

theorem drop_prem {s : Stage} {t : SyntacticTerm LIinfW} {φ : Proposition LIinfW}
    {H : Set ThetaVNoteD → Set ThetaVNoteD} {α₀ : ThetaVNoteD} {Δ Γ : Sequent LIinfW}
    (hH : ThetaVNoteD.IsOperator H) (d₀ : IDwDerivable A ρ H α₀ (φ :: Δ))
    (ih₀ : DropClaim A ρ s t H α₀ (φ :: Δ)) (hΔ : Δ ⊆ stageAt s t :: Γ)
    (hP : paramsVal Γ ⊆ H ∅) : IDwDerivable A ρ H α₀ (φ :: Γ) := by
  refine ih₀ hH (φ :: Γ) ?_ ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rcases List.mem_cons.mp (hΔ hx) with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  · rw [paramsVal_cons]
    exact Set.union_subset d₀.params_head_subset hP

theorem drop_aux {s : Stage} (hs : s.val = ThetaVNoteD.zero) {t : SyntacticTerm LIinfW}
    {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Δ : Sequent LIinfW}
    (d : IDwDerivable A ρ H α Δ) : DropClaim A ρ s t H α Δ := by
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
    have hv : a.1 = ThetaVNoteD.zero := by
      have := congrArg Stage.val e
      exact this.trans hs
    rw [hv] at hga
    exact absurd hga (not_lt_of_ge (ThetaVNoteD.zero_le' _))
  | @nstage H' α' Δ' j a t' f hα _ hm hf d0 ih0 =>
    intro hH Γ hΔ hP
    refine .nstage f hα hP (drop_mem hm hΔ fun h => nomatch h) hf fun g hg => ?_
    have hsub : H' ∅ ⊆ ThetaVNoteD.adjoin H' {g.1} ∅ := hH.mono (Set.empty_subset _)
    exact drop_prem (hH.adjoin {g.1}) (d0 g hg) (ih0 g hg) hΔ (hP.trans hsub)
  | @fix H' α' Δ' j t' α₀ hα _ hm hΩ h0 d0 ih0 =>
    intro hH Γ hΔ hP
    refine .fix hα hP (drop_mem hm hΔ fun h => ?_) hΩ h0 (drop_prem hH d0 ih0 hΔ hP)
    obtain ⟨e, -⟩ := stageAt_inj h
    have := congrArg Stage.val e
    rw [Stage.val_top, hs] at this
    exact absurd this (ne_of_gt (ThetaVNoteD.zero_lt_Omega _))
  | jlev hα _ hm hs' ht' hl h0 d0 ih0 =>
    intro hH Γ hΔ hP
    refine .jlev hα hP (drop_mem hm hΔ fun h => ?_) hs' ht' hl h0 (drop_prem hH d0 ih0 hΔ hP)
    have := congrArg posHeadStage h
    exact nomatch this
  | njlev hα _ hm hs' ht' h0 d0 ih0 =>
    intro hH Γ hΔ hP
    exact .njlev hα hP (drop_mem hm hΔ fun h => nomatch h) hs' ht' h0
      fun hl => drop_prem hH (d0 hl) (ih0 hl) hΔ hP
  | cut hα _ hr h0 d0 d1 ih0 ih1 =>
    intro hH Γ hΔ hP
    exact .cut hα hP hr h0 (drop_prem hH d0 ih0 hΔ hP) (drop_prem hH d1 ih1 hΔ hP)

/-- **The empty disjunction `I_j^{≺0} t` can be dropped**: `H ⊢^α_ρ Γ, I_j^{≺0} t` gives
`H ⊢^α_ρ Γ` (`I_j^{≺0} t ≃ ⋁_{γ ≺ 0}`, so it is never the principal formula of a clause). -/
theorem drop_stage_zero {s : Stage} (hs : s.val = ThetaVNoteD.zero)
    {t : SyntacticTerm LIinfW} {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD}
    {Γ : Sequent LIinfW} (hH : ThetaVNoteD.IsOperator H)
    (d : IDwDerivable A ρ H α (stageAt s t :: Γ)) : IDwDerivable A ρ H α Γ := by
  refine drop_aux hs d hH Γ (List.Subset.refl _) ?_
  have h := d.params_subset
  rw [paramsVal_cons] at h
  exact Set.subset_union_right.trans h

end Drop

end Collapsing

end IDw

end OrdinalAnalysis
