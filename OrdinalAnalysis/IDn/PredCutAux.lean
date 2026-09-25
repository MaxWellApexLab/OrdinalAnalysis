/-
  Shared context of predicative cut elimination for `ID_n` (`IDn/PredCut.lean`, Buchholz 1992
  Theorem 3.16 per level): the total Veblen function `phiN`, the closure condition `PhiClosed`,
  the claim `PredCutClaim` of the outer (well-founded, on the cut rank) induction, and the facts
  every case of the inner (derivation) induction `IDn/PredCutCases/*` uses.

  Source: W. Buchholz, *A simplified version of local predicativity* (1992), §1 (the axioms
  (φ.1)–(φ.4) of the `φ`-hierarchy), Theorem 3.16; A. Freund, arXiv:2204.09321, Definition 7.6,
  Lemma 7.7, Theorem 7.8 (one level).

  **The form used here.**  Buchholz 3.16 reads `H ⊢^α_{γ+ω^ρ} Γ ⇒ H ⊢^{φρα}_γ Γ` when no `Ω_σ`
  lies in `[γ, γ+ω^ρ)`.  Here the Veblen index is the cut rank `r` itself:

      H ⊢^α_r Γ   ⇒   H ⊢^{φ_k(r, α)}_μ Γ,     r, α ≺ Ω_{k+1},  no `Ω_j` in `[μ, Ω_{k+1})`.

  Since `φ_k(r, ·)` only grows with `r` (φ.4), this is the same bound up to the choice of index
  and needs no Cantor-normal-form decomposition of the rank segment: a cut of rank `c ∈ [μ, r)`
  is removed by one step of Exercise 7.1 (c) (`IDnDerivable.elimination`, rank `c + 1 ↦ c`) and
  the outer induction hypothesis at `c < r`.

  * `phiN k r a`        `φ_k(r, a) = ϑ_k(Ω_{k+1}·r + a)` as a `ThetaWNoteD` (`0` off the domain
                        `r, a ≺ Ω_{k+1}`, where it is never used).
  * `PhiClosed k H`     every `H(Z)` is closed under `φ_k` on `Ω_{k+1}` (Buchholz, Lemma 4.6 b)).
  * `PredCutClaim`      the statement proved for every rank `r ≺ Ω_{k+1}`.
  * the order facts     (φ.1) `lt_phiN_self`, (φ.3) `phiN_lt_phiN_right`, (φ.4)
                        `phiN_lt_phiN_left`, principality `isPrin_phiN`, `phiN_lt_Omega`.
  * `phiClosed_HopS`    the operator `H_γ` is `φ_k`-closed once `ω^{(Ω_{k+1}+1)·2} ⪯ γ`
                        (the hypothesis `CollapseHyps.predCut` carries).
  * `noOmega_muBar`     `[Ω_s + 1, Ω_{s+1})` contains no `Ω_j`.
-/
import OrdinalAnalysis.IDn.Elimination
import OrdinalAnalysis.IDn.Collapsing.Basic
import OrdinalAnalysis.Ordinal.ThetaW.VeblenOrder2
import OrdinalAnalysis.Ordinal.ThetaW.WellFoundedD

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWNoteD

open ThetaWTerm

/-! ### The total Veblen function and its order facts -/

/-- `φ_k(r, a)` bundled with its domain proof, for `r, a ≺ Ω_{k+1}`. -/
def phiD (k : ℕ) (r a : ThetaWNoteD) (hr : r < Omega k) (ha : a < Omega k) : ThetaWNoteD :=
  ⟨phi k r a, nf_phi k r a, dom_phi_of_lt hr ha⟩

/-- `φ_k(r, a) = ϑ_k(Ω_{k+1}·r + a)` (`ThetaW/Veblen.lean`'s `phi`) bundled as a domain
notation when `r, a ≺ Ω_{k+1}` (`dom_phi_of_lt`), and `0` otherwise. -/
def phiN (k : ℕ) (r a : ThetaWNoteD) : ThetaWNoteD :=
  if h : r < Omega k ∧ a < Omega k then phiD k r a h.1 h.2 else zero

theorem phiN_val {k : ℕ} {r a : ThetaWNoteD} (hr : r < Omega k) (ha : a < Omega k) :
    (phiN k r a).1 = phi k r a := by
  unfold phiN
  rw [dif_pos (show r < Omega k ∧ a < Omega k from ⟨hr, ha⟩)]
  rfl

theorem isPrin_phiN {k : ℕ} {r a : ThetaWNoteD} (hr : r < Omega k) (ha : a < Omega k) :
    IsPrin (phiN k r a).1 := by
  rw [phiN_val hr ha]
  exact isPrin_theta k _

theorem phiN_lt_Omega (k : ℕ) (r a : ThetaWNoteD) : phiN k r a < Omega k := by
  by_cases h : r < Omega k ∧ a < Omega k
  · rw [lt_iff, phiN_val h.1 h.2]
    exact theta_lt_Omega_self k _
  · unfold phiN
    rw [dif_neg h]
    exact nil_lt_Omega _

/-- **(φ.3)** `φ_k(r, ·)` is strictly monotone. -/
theorem phiN_lt_phiN_right {k : ℕ} {r a a' : ThetaWNoteD} (hr : r < Omega k)
    (ha : a < Omega k) (ha' : a' < Omega k) (h : a < a') : phiN k r a < phiN k r a' := by
  rw [lt_iff, phiN_val hr ha, phiN_val hr ha']
  exact phi_lt_phi_right hr ha ha' h

/-- **(φ.1)** `a ≺ φ_k(r, a)`. -/
theorem lt_phiN_self {k : ℕ} {r a : ThetaWNoteD} (hr : r < Omega k) (ha : a < Omega k) :
    a < phiN k r a := by
  rw [lt_iff, phiN_val hr ha]
  exact lt_phi_right_self hr ha

/-- **(φ.4)** `c ≺ r` and `b ≺ φ_k(r, a)` give `φ_k(c, b) ≺ φ_k(r, a)`. -/
theorem phiN_lt_phiN_left {k : ℕ} {c r b a : ThetaWNoteD} (hc : c < Omega k)
    (hr : r < Omega k) (hb : b < Omega k) (ha : a < Omega k) (hcr : c < r)
    (hba : b < phiN k r a) : phiN k c b < phiN k r a := by
  rw [lt_iff, phiN_val hr ha] at hba
  rw [lt_iff, phiN_val hc hb, phiN_val hr ha]
  exact phi_lt_phi_of_lt_left hc hr hb ha hcr hba

/-! ### `φ_k`-closed operators -/

/-- **`H` is closed under `φ_k` on `Ω_{k+1}`**: `r, a ∈ H(Z)`, `r, a ≺ Ω_{k+1}` give
`φ_k(r, a) ∈ H(Z)` (Buchholz, Lemma 4.6 b), for the operators of the step (□)). -/
def PhiClosed (k : ℕ) (H : Set ThetaWNoteD → Set ThetaWNoteD) : Prop :=
  ∀ (Z : Set ThetaWNoteD) (r a : ThetaWNoteD), r < Omega k → a < Omega k → r ∈ H Z → a ∈ H Z →
    phiN k r a ∈ H Z

theorem PhiClosed.adjoin {k : ℕ} {H : Set ThetaWNoteD → Set ThetaWNoteD} (h : PhiClosed k H)
    (W : Set ThetaWNoteD) : PhiClosed k (ThetaWNoteD.adjoin H W) :=
  fun Z r a hr ha hrZ haZ => h (W ∪ Z) r a hr ha hrZ haZ

theorem mem_Atoms_of_mem_Atoms_omegaAdd {k : ℕ} {e g : ThetaWTerm}
    (h : g ∈ Atoms (omegaAdd k e)) : g ∈ Atoms e := by
  unfold omegaAdd at h
  obtain ⟨x, hx, hg⟩ := mem_Atoms_ofList.mp h
  rcases mem_addL hx with hx | hx
  · rw [List.mem_singleton.mp hx] at hg; simp at hg
  · exact mem_Atoms_iff_toList.mpr ⟨x, hx, hg⟩

theorem Ahull_omegaMulOmega_subset (k : ℕ) (a : ThetaWNoteD) :
    Ahull (omegaMulOmega k a) ⊆ Ahull a := by
  intro g hg
  obtain ⟨e, he, hge⟩ := mem_Ahull_iff_entries.mp hg
  rw [entries_omegaMulOmega] at he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  exact mem_Ahull_iff_entries.mpr ⟨d, hd, mem_Atoms_of_mem_Atoms_omegaAdd hge⟩

theorem NiceS.omegaMulOmega_mem {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : NiceS H)
    {X : Set ThetaWNoteD} (k : ℕ) {a : ThetaWNoteD} (ha : a ∈ H X) : omegaMulOmega k a ∈ H X :=
  hH.mem_iff.mpr ((Ahull_omegaMulOmega_subset k a).trans (hH.mem_iff.mp ha))

/-- The argument `Ω_{k+1}·r + a` of `φ_k` lies below `ω^{(Ω_{k+1}+1)+(Ω_{k+1}+1)}`. -/
theorem phiArg_lt_omegaPow {k : ℕ} {r a : ThetaWNoteD} (hr : r < Omega k) (ha : a < Omega k) :
    phiArg k r a < omegaPow ((Omega k + one) + (Omega k + one)) := by
  have hΩ : Omega k ≤ (Omega k + one) + (Omega k + one) :=
    le_trans (ThetaWNoteD.le_add_right _ _) (ThetaWNoteD.le_add_right _ _)
  rw [lt_omegaPow_iff, entries_phiArg_eq_of_lt hr ha]
  intro e he
  rcases List.mem_append.mp he with he | he
  · rw [entries_omegaMulOmega] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    let E : ThetaWNoteD := ⟨e0, (cnf_entries r).nf he0, dom_entries r e0 he0⟩
    have hE : E < Omega k := (lt_prin_iff (isPrin_Omega k)).mp hr e0 he0
    have heq : omegaAdd k e0 = (Omega k + E).1 := rfl
    rw [heq]
    show Omega k + E < (Omega k + one) + (Omega k + one)
    rw [ThetaWNoteD.add_assoc]
    refine ThetaWNoteD.add_lt_add_left _ (lt_of_lt_of_le hE ?_)
    exact le_trans (ThetaWNoteD.le_add_left one (Omega k))
      (ThetaWNoteD.add_le_add_left one (ThetaWNoteD.le_add_right _ _))
  · exact lt_of_lt_of_le' ((lt_prin_iff (isPrin_Omega k)).mp ha e he) hΩ

/-- **`H_γ` is `φ_k`-closed** once `ω^{(Ω_{k+1}+1)+(Ω_{k+1}+1)} ⪯ γ` (`theta_mem_HopS`: the
argument `Ω_{k+1}·r + a` is in `H_γ(Z)` and `⪯ γ`). -/
theorem phiClosed_HopS {k : ℕ} {γ : ThetaWNoteD}
    (hγ : omegaPow ((Omega k + one) + (Omega k + one)) ≤ γ) : PhiClosed k (HopS γ) := by
  intro Z r a hr ha hrZ haZ
  have hdom : Dom (ThetaWTerm.theta k (phiArg k r a).1) := dom_phi_of_lt hr ha
  have hx : phiArg k r a ∈ HopS γ Z :=
    (HopS_nice γ).add_mem ((HopS_nice γ).omegaMulOmega_mem k hrZ) haZ
  have hxb : phiArg k r a ≤ γ := le_of_lt (lt_of_lt_of_le (phiArg_lt_omegaPow hr ha) hγ)
  have h := theta_mem_HopS k hx hxb hdom
  have he : phiN k r a = thetaD k (phiArg k r a) hdom := Subtype.ext (by
    rw [phiN_val hr ha]; rfl)
  rw [he]
  exact h

end ThetaWNoteD

namespace IDn

open LO LO.FirstOrder

variable {n : ℕ}

/-- `[Ω_s + 1, Ω_{s+1})` (Lean: `[Omega s + 1, Omega (s+1))`) contains no `Ω_j`. -/
theorem noOmega_muBar (s : ℕ) :
    ∀ c : ThetaWNoteD, Collapsing.muBar (s + 1) ≤ c → c < ThetaWNoteD.Omega (s + 1) →
      ∀ j : Fin n, c ≠ ThetaWNoteD.Omega j.val := by
  intro c h1 h2 j heq
  subst heq
  rw [Collapsing.muBar_succ] at h1
  rcases Nat.lt_or_ge j.val (s + 1) with hj | hj
  · have hle : ThetaWNoteD.Omega j.val ≤ ThetaWNoteD.Omega s := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | h
      · exact le_of_lt (ThetaWNoteD.Omega_lt_Omega_iff.mpr h)
      · rw [h]
    exact absurd (lt_of_le_of_lt hle (lt_of_lt_of_le (ThetaWNoteD.Omega_lt_Omega_add_one s) h1))
      (lt_irrefl _)
  · have hle : ThetaWNoteD.Omega (s + 1) ≤ ThetaWNoteD.Omega j.val := by
      rcases Nat.lt_or_eq_of_le hj with h | h
      · exact le_of_lt (ThetaWNoteD.Omega_lt_Omega_iff.mpr h)
      · rw [h]
    exact absurd (lt_of_lt_of_le h2 hle) (lt_irrefl _)

/-- **The claim of the outer induction, at cut rank `r`**: every `H ⊢^α_r Γ` with `H` nice and
`φ_k`-closed, `r ∈ H(∅)` and `α ≺ Ω_{k+1}` gives `H ⊢^{φ_k(r, α)}_μ Γ`. -/
def PredCutClaim (A : Fin n → Semisentence (LXIn n) 1) (k : ℕ) (μ r : ThetaWNoteD) : Prop :=
  ∀ {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)},
    IDnDerivable A r H α Γ → ThetaWNoteD.NiceS H → ThetaWNoteD.PhiClosed k H → r ∈ H ∅ →
      α < ThetaWNoteD.Omega k → IDnDerivable A μ H (ThetaWNoteD.phiN k r α) Γ

end IDn

end OrdinalAnalysis
