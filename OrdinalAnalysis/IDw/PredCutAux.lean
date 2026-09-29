/- Source: OrdinalAnalysis\IDn\PredCutAux.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.Calculus
import OrdinalAnalysis.Ordinal.ThetaV.HullSingle
import OrdinalAnalysis.Ordinal.ThetaV.VeblenOrder2
import OrdinalAnalysis.Ordinal.ThetaV.WellFoundedV
/-
  Shared context of predicative cut elimination for `ID_ω` (`IDw/PredCut.lean`, Buchholz 1992
  Theorem 3.16 per level): the total Veblen function `phiN`, the closure condition `PhiClosed`,
  the claim `PredCutClaim` of the outer (well-founded, on the cut rank) induction, and the facts
  every case of the inner (derivation) induction `IDw/PredCutCases/*` uses.

  Source: W. Buchholz, *A simplified version of local predicativity* (1992), §1 (the axioms
  (φ.1)–(φ.4) of the `φ`-hierarchy), Theorem 3.16; A. Freund, arXiv:2204.09321, Definition 7.6,
  Lemma 7.7, Theorem 7.8 (one level).

  **The form used here.**  Buchholz 3.16 reads `H ⊢^α_{γ+ω^ρ} Γ ⇒ H ⊢^{φρα}_γ Γ` when no `Ω_σ`
  lies in `[γ, γ+ω^ρ)`.  Here the Veblen index is the cut rank `r` itself:

      H ⊢^α_r Γ   ⇒   H ⊢^{φ_k(r, α)}_μ Γ,     r, α ≺ Ω_{k+1},  no `Ω_j` in `[μ, Ω_{k+1})`.

  Since `φ_k(r, ·)` only grows with `r` (φ.4), this is the same bound up to the choice of index
  and needs no Cantor-normal-form decomposition of the rank segment: a cut of rank `c ∈ [μ, r)`
  is removed by one step of Exercise 7.1 (c) (`IDwDerivable.elimination`, rank `c + 1 ↦ c`) and
  the outer induction hypothesis at `c < r`.

  * `phiN k r a`        `φ_k(r, a) = ϑ_k(Ω_{k+1}·r + a)` as a `ThetaVNoteD` (`0` off the domain
                        `r, a ≺ Ω_{k+1}`, where it is never used).
  * `PhiClosed k H`     every `H(Z)` is closed under `φ_k` on `Ω_{k+1}` (Buchholz, Lemma 4.6 b)).
  * `PredCutClaim`      the statement proved for every rank `r ≺ Ω_{k+1}`.
  * the order facts     (φ.1) `lt_phiN_self`, (φ.3) `phiN_lt_phiN_right`, (φ.4)
                        `phiN_lt_phiN_left`, principality `isPrin_phiN`, `phiN_lt_Omega`.
  * `phiClosed_HopS`    the operator `H_γ` is `φ_k`-closed once `ω^{(Ω_{k+1}+1)·2} ⪯ γ`
                        (the hypothesis `CollapseHyps.predCut` carries).
  * `noOmega_muBar`     `[Ω_s + 1, Ω_{s+1})` contains no `Ω_j`.
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaVNoteD

open ThetaVTerm

/-! ### The total Veblen function and its order facts -/

/-- `φ_k(r, a)` bundled with its domain proof, for `r, a ≺ Ω_{k+1}`. -/
def phiD (k : ℕ) (r a : ThetaVNoteD) (hr : r < Omega k) (ha : a < Omega k) : ThetaVNoteD :=
  ⟨phi k r a, nf_phi k r a, dom_phi_of_lt hr ha⟩

/-- `φ_k(r, a) = ϑ_k(Ω_{k+1}·r + a)` (`ThetaW/Veblen.lean`'s `phi`) bundled as a domain
notation when `r, a ≺ Ω_{k+1}` (`dom_phi_of_lt`), and `0` otherwise. -/
def phiN (k : ℕ) (r a : ThetaVNoteD) : ThetaVNoteD :=
  if h : r < Omega k ∧ a < Omega k then phiD k r a h.1 h.2 else zero

theorem phiN_val {k : ℕ} {r a : ThetaVNoteD} (hr : r < Omega k) (ha : a < Omega k) :
    (phiN k r a).1 = phi k r a := by
  unfold phiN
  rw [dif_pos (show r < Omega k ∧ a < Omega k from ⟨hr, ha⟩)]
  rfl

theorem isPrin_phiN {k : ℕ} {r a : ThetaVNoteD} (hr : r < Omega k) (ha : a < Omega k) :
    IsPrin (phiN k r a).1 := by
  rw [phiN_val hr ha]
  exact isPrin_theta k _

theorem phiN_lt_Omega (k : ℕ) (r a : ThetaVNoteD) : phiN k r a < Omega k := by
  by_cases h : r < Omega k ∧ a < Omega k
  · rw [lt_iff, phiN_val h.1 h.2]
    exact theta_lt_Omega_self k _
  · unfold phiN
    rw [dif_neg h]
    exact nil_lt_Omega _

/-- **(φ.3)** `φ_k(r, ·)` is strictly monotone. -/
theorem phiN_lt_phiN_right {k : ℕ} {r a a' : ThetaVNoteD} (hr : r < Omega k)
    (ha : a < Omega k) (ha' : a' < Omega k) (h : a < a') : phiN k r a < phiN k r a' := by
  rw [lt_iff, phiN_val hr ha, phiN_val hr ha']
  exact phi_lt_phi_right hr ha ha' h

/-- **(φ.1)** `a ≺ φ_k(r, a)`. -/
theorem lt_phiN_self {k : ℕ} {r a : ThetaVNoteD} (hr : r < Omega k) (ha : a < Omega k) :
    a < phiN k r a := by
  rw [lt_iff, phiN_val hr ha]
  exact lt_phi_right_self hr ha

/-- **(φ.4)** `c ≺ r` and `b ≺ φ_k(r, a)` give `φ_k(c, b) ≺ φ_k(r, a)`. -/
theorem phiN_lt_phiN_left {k : ℕ} {c r b a : ThetaVNoteD} (hc : c < Omega k)
    (hr : r < Omega k) (hb : b < Omega k) (ha : a < Omega k) (hcr : c < r)
    (hba : b < phiN k r a) : phiN k c b < phiN k r a := by
  rw [lt_iff, phiN_val hr ha] at hba
  rw [lt_iff, phiN_val hc hb, phiN_val hr ha]
  exact phi_lt_phi_of_lt_left hc hr hb ha hcr hba

/-! ### `φ_k`-closed operators -/

/-- **`H` is closed under `φ_k` on `Ω_{k+1}`**: `r, a ∈ H(Z)`, `r, a ≺ Ω_{k+1}` give
`φ_k(r, a) ∈ H(Z)` (Buchholz, Lemma 4.6 b), for the operators of the step (□)). -/
def PhiClosed (k : ℕ) (H : Set ThetaVNoteD → Set ThetaVNoteD) : Prop :=
  ∀ (Z : Set ThetaVNoteD) (r a : ThetaVNoteD), r < Omega k → a < Omega k → r ∈ H Z → a ∈ H Z →
    phiN k r a ∈ H Z

theorem PhiClosed.adjoin {k : ℕ} {H : Set ThetaVNoteD → Set ThetaVNoteD} (h : PhiClosed k H)
    (W : Set ThetaVNoteD) : PhiClosed k (ThetaVNoteD.adjoin H W) :=
  fun Z r a hr ha hrZ haZ => h (W ∪ Z) r a hr ha hrZ haZ

theorem mem_Atoms_of_mem_Atoms_omegaAdd {k : ℕ} {e g : ThetaVTerm}
    (h : g ∈ Atoms (omegaAdd k e)) : g ∈ Atoms e := by
  unfold omegaAdd at h
  obtain ⟨x, hx, hg⟩ := mem_Atoms_ofList.mp h
  rcases mem_addL hx with hx | hx
  · rw [List.mem_singleton.mp hx] at hg; simp at hg
  · exact mem_Atoms_iff_toList.mpr ⟨x, hx, hg⟩

theorem Ahull_omegaMulOmega_subset (k : ℕ) (a : ThetaVNoteD) :
    Ahull (omegaMulOmega k a) ⊆ Ahull a := by
  intro g hg
  obtain ⟨e, he, hge⟩ := mem_Ahull_iff_entries.mp hg
  rw [entries_omegaMulOmega] at he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  exact mem_Ahull_iff_entries.mpr ⟨d, hd, mem_Atoms_of_mem_Atoms_omegaAdd hge⟩

theorem NiceS.omegaMulOmega_mem {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : NiceS H)
    {X : Set ThetaVNoteD} (k : ℕ) {a : ThetaVNoteD} (ha : a ∈ H X) : omegaMulOmega k a ∈ H X :=
  hH.mem_iff.mpr ((Ahull_omegaMulOmega_subset k a).trans (hH.mem_iff.mp ha))

/-- The argument `Ω_{k+1}·r + a` of `φ_k` lies below `ω^{(Ω_{k+1}+1)+(Ω_{k+1}+1)}`. -/
theorem phiArg_lt_omegaPow {k : ℕ} {r a : ThetaVNoteD} (hr : r < Omega k) (ha : a < Omega k) :
    phiArg k r a < omegaPow ((Omega k + one) + (Omega k + one)) := by
  have hΩ : Omega k ≤ (Omega k + one) + (Omega k + one) :=
    le_trans (ThetaVNoteD.le_add_right _ _) (ThetaVNoteD.le_add_right _ _)
  rw [lt_omegaPow_iff, entries_phiArg_eq_of_lt hr ha]
  intro e he
  rcases List.mem_append.mp he with he | he
  · rw [entries_omegaMulOmega] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    let E : ThetaVNoteD := ⟨e0, (cnf_entries r).nf he0, dom_entries r e0 he0⟩
    have hE : E < Omega k := (lt_prin_iff (isPrin_Omega k)).mp hr e0 he0
    have heq : omegaAdd k e0 = (Omega k + E).1 := rfl
    rw [heq]
    show Omega k + E < (Omega k + one) + (Omega k + one)
    rw [ThetaVNoteD.add_assoc]
    refine ThetaVNoteD.add_lt_add_left _ (lt_of_lt_of_le hE ?_)
    exact le_trans (ThetaVNoteD.le_add_left one (Omega k))
      (ThetaVNoteD.add_le_add_left one (ThetaVNoteD.le_add_right _ _))
  · exact lt_of_lt_of_le' ((lt_prin_iff (isPrin_Omega k)).mp ha e he) hΩ

/-- **`H_γ` is `φ_k`-closed** once `ω^{(Ω_{k+1}+1)+(Ω_{k+1}+1)} ⪯ γ` (`theta_mem_HopS`: the
argument `Ω_{k+1}·r + a` is in `H_γ(Z)` and `⪯ γ`). -/
theorem phiClosed_HopS {k : ℕ} {γ : ThetaVNoteD}
    (hγ : omegaPow ((Omega k + one) + (Omega k + one)) ≤ γ) : PhiClosed k (HopS γ) := by
  intro Z r a hr ha hrZ haZ
  have hdom : Dom (ThetaVTerm.theta k (phiArg k r a).1) := dom_phi_of_lt hr ha
  have hx : phiArg k r a ∈ HopS γ Z :=
    (HopS_nice γ).add_mem ((HopS_nice γ).omegaMulOmega_mem k hrZ) haZ
  have hxb : phiArg k r a ≤ γ := le_of_lt (lt_of_lt_of_le (phiArg_lt_omegaPow hr ha) hγ)
  have h := theta_mem_HopS k hx hxb hdom
  have he : phiN k r a = thetaD k (phiArg k r a) hdom := Subtype.ext (by
    rw [phiN_val hr ha]; rfl)
  rw [he]
  exact h

end ThetaVNoteD

namespace IDw

open LO LO.FirstOrder


/-- `[Ω_s + 1, Ω_{s+1})` (Lean: `[Omega s + 1, Omega (s+1))`) contains no `Ω_j`. -/
theorem noOmega_muBar (s : ℕ) :
    ∀ c : ThetaVNoteD, ThetaVNoteD.Omega s + ThetaVNoteD.one ≤ c → c < ThetaVNoteD.Omega (s + 1) →
      ∀ j : ℕ, c ≠ ThetaVNoteD.Omega j := by
  intro c h1 h2 j heq
  subst heq
  have hΩ : ThetaVNoteD.Omega s < ThetaVNoteD.Omega s + ThetaVNoteD.one := by
    have h := ThetaVNoteD.add_lt_add_left (ThetaVNoteD.Omega s) ThetaVNoteD.zero_lt_one
    rwa [ThetaVNoteD.add_zero] at h
  rcases Nat.lt_or_ge j (s + 1) with hj | hj
  · have hle : ThetaVNoteD.Omega j ≤ ThetaVNoteD.Omega s := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | h
      · exact le_of_lt (ThetaVNoteD.Omega_lt_Omega_iff.mpr h)
      · rw [h]
    exact absurd (lt_of_le_of_lt hle (lt_of_lt_of_le hΩ h1))
      (lt_irrefl _)
  · have hle : ThetaVNoteD.Omega (s + 1) ≤ ThetaVNoteD.Omega j := by
      rcases Nat.lt_or_eq_of_le hj with h | h
      · exact le_of_lt (ThetaVNoteD.Omega_lt_Omega_iff.mpr h)
      · rw [h]
    exact absurd (lt_of_lt_of_le h2 hle) (lt_irrefl _)

/-- **Freund, Exercise 5.5 (e), `Jlev`-honest form** (the port of `IDn.rk_mem_of_closed`, which
`IDw/CalculusAux.lean` deliberately leaves unported): the rank of a formula with no `Jlev ⊤` atom
lies in every set that contains `0`, the atom rank of every stage parameter, and the atom rank
`Ω_j + 1` of every `Jlev j` (`j : ℕ`; these carry no parameters, `params (Jlev ..) = ∅`), and is
closed under `+ 1`. The `NoJlevTop` hypothesis is needed: `rk (Jlev ⊤ ..) = Ω_ω`. -/
theorem rk_mem_of_closed_noJlevTop {ξ : Type*} {m : ℕ} {S : Set ThetaVNoteD}
    (h0 : ThetaVNoteD.zero ∈ S) (hsucc : ∀ x ∈ S, ThetaVNoteD.succ x ∈ S)
    (hj : ∀ j : ℕ, ThetaVNoteD.succ (ThetaVNoteD.OmegaBelow j) ∈ S)
    {φ : Semiformula LIinfW ξ m} (hJ : NoJlevTop φ)
    (h : ∀ s ∈ params φ, atomRkStage s ∈ S) : rk φ ∈ S := by
  have hmax : ∀ x y : ThetaVNoteD, x ∈ S → y ∈ S → max x y ∈ S := fun x y hx hy => by
    rcases le_total x y with hxy | hxy
    · rw [max_eq_right hxy]; exact hy
    · rw [max_eq_left hxy]; exact hx
  induction φ using Semiformula.rec' with
  | hverum => rw [rk_verum]; exact h0
  | hfalsum => rw [rk_falsum]; exact h0
  | hrel r v =>
    rw [rk_rel]
    rcases r with r | r
    · exact h0
    · cases r with
      | X => exact h0
      | stage s => exact h s rfl
      | jlev ℓ =>
        induction ℓ using WithTop.recTopCoe with
        | top => exact absurd rfl hJ
        | coe j => exact hj j
  | hnrel r v =>
    rw [rk_nrel]
    rcases r with r | r
    · exact h0
    · cases r with
      | X => exact h0
      | stage s => exact h s rfl
      | jlev ℓ =>
        induction ℓ using WithTop.recTopCoe with
        | top => exact absurd rfl hJ
        | coe j => exact hj j
  | hand φ ψ ihφ ihψ =>
    rw [rk_and]
    exact hsucc _ (hmax _ _ (ihφ hJ.1 fun s hs => h s (Or.inl hs))
      (ihψ hJ.2 fun s hs => h s (Or.inr hs)))
  | hor φ ψ ihφ ihψ =>
    rw [rk_or]
    exact hsucc _ (hmax _ _ (ihφ hJ.1 fun s hs => h s (Or.inl hs))
      (ihψ hJ.2 fun s hs => h s (Or.inr hs)))
  | hall φ ih => rw [rk_all]; exact hsucc _ (ih hJ h)
  | hexs φ ih => rw [rk_exs]; exact hsucc _ (ih hJ h)

/-- **Freund, Exercise 5.5 (e)**, for a nice operator: the parameters' values in `H(X)` give
`rk(ψ) ∈ H(X)` for a formula with no `Jlev ⊤` atom. -/
theorem _root_.OrdinalAnalysis.ThetaVNoteD.NiceS.rk_mem_of_noJlevTop
    {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H) {X : Set ThetaVNoteD}
    {ξ : Type*} {m : ℕ} {φ : Semiformula LIinfW ξ m} (hJ : NoJlevTop φ)
    (h : ∀ s ∈ params φ, s.val ∈ H X) : rk φ ∈ H X :=
  rk_mem_of_closed_noJlevTop hH.zero_mem (fun _ hx => hH.succ_mem hx)
    (fun j => hH.succ_mem (hH.omegaBelow_mem X j)) hJ (fun s hs => hH.atomRkStage_mem (h s hs))

/-- **The claim of the outer induction, at cut rank `r`**: every `H ⊢^α_r Γ` with `H` nice and
`φ_k`-closed, `r ∈ H(∅)` and `α ≺ Ω_{k+1}` gives `H ⊢^{φ_k(r, α)}_μ Γ`. -/
def PredCutClaim (A : Semisentence LForm 2) (k : ℕ) (μ r : ThetaVNoteD) : Prop :=
  ∀ {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent (LIinfW)},
    IDwDerivable A r H α Γ → ThetaVNoteD.NiceS H → ThetaVNoteD.PhiClosed k H → r ∈ H ∅ →
      α < ThetaVNoteD.Omega k → IDwDerivable A μ H (ThetaVNoteD.phiN k r α) Γ

end IDw

end OrdinalAnalysis
