import OrdinalAnalysis.KPi.Ord.Closure

/-!
# Buchholz 1992, Def 4.2: the collapsing functions `ψ_κ`; Lemma 4.4 (c), (d), Lemma 4.5 (a)

`psiK κ α = ψ_κ α = min {β | κ ∈ C(α, β) ∧ C(α, β) ∩ κ ⊆ β}`, defined by well-founded recursion on `α`
(the closure `C(α, β)` only uses `ψ_π ξ` for `ξ < α`).  Totality of the defining set for `κ ∈ R`
is Lemma 4.5 (a); for `κ ∉ R` the value is junk and never used.

* `psiK_lt`, `psiK_not_mem_Ck` : Lemma 4.5 (a);
* `kappa_mem_C` : Lemma 4.4 (c);   `Ck_inter` : Lemma 4.4 (d).

Lemmas 4.4 (c), (d) depend on the totality 4.5 (a) and are therefore proved after it.
-/

set_option autoImplicit false

open Ordinal Cardinal Set Order

noncomputable section

namespace OrdinalAnalysis.KPi.Ord

/-- One step of the recursion: `ih ξ _ π = ψ_π ξ` for `ξ < α`. -/
def psiF (α : O) (ih : ∀ ξ, ξ < α → O → O) (κ : O) : O :=
  sInf {β | Cl (fun π ξ => if h : ξ < α then ih ξ h π else 0) α β κ ∧
    ∀ x, Cl (fun π ξ => if h : ξ < α then ih ξ h π else 0) α β x → x < κ → x < β}

def psiFix : O → O → O :=
  WellFounded.fix (C := fun _ => O → O) (wellFounded_lt (α := O)) (fun α ih => psiF α ih)

/-- B92 Def 4.2: `ψ_κ α`. -/
def psiK (κ α : O) : O := psiFix α κ

theorem psiFix_eq (α : O) : psiFix α = psiF α (fun ξ _ => psiFix ξ) :=
  WellFounded.fix_eq _ _ _

/-- The closure sets `C(α,β)` of B92 Def 4.2. -/
def C (α β : O) : Set O := {x | Cl psiK α β x}

theorem mem_C {α β x : O} : x ∈ C α β ↔ Cl psiK α β x := Iff.rfl

/-- `C_κ(α) := C(α, ψ_κ α)`. -/
def Ck (κ α : O) : Set O := C α (psiK κ α)

theorem psiK_def (κ α : O) :
    psiK κ α = sInf {β | Cl psiK α β κ ∧ ∀ x, Cl psiK α β x → x < κ → x < β} := by
  have h1 : psiK κ α = psiF α (fun ξ _ => psiFix ξ) κ := by
    unfold psiK; rw [psiFix_eq α]
  rw [h1, psiF]
  have hg : ∀ ξ, ξ < α → ∀ π, (fun π ξ => if h : ξ < α then psiFix ξ π else 0) π ξ = psiK π ξ := by
    intro ξ hξ π; simp [hξ, psiK]
  have hcl : ∀ β x, Cl (fun π ξ => if h : ξ < α then psiFix ξ π else 0) α β x ↔ Cl psiK α β x := by
    intro β x
    constructor
    · exact Cl.congr (fun ξ hξ π => (hg ξ hξ π))
    · exact Cl.congr (fun ξ hξ π => (hg ξ hξ π).symm)
  congr 1
  ext β
  simp only [Set.mem_ofPred_eq, hcl]

/-- The defining set of `ψ_κ α`. -/
def PsiSet (κ α : O) : Set O := {β | Cl psiK α β κ ∧ ∀ x, Cl psiK α β x → x < κ → x < β}

theorem psiK_eq_sInf (κ α : O) : psiK κ α = sInf (PsiSet κ α) := psiK_def κ α

lemma Iord_pos : 0 < Iord := by
  have := isRU_Iord.reg.pos
  rw [pos_iff_ne_zero]
  intro h0
  rw [h0] at this
  simp at this

lemma Om_succ (σ : O) : Om (σ + 1) = ω_ (σ + 1) := by simp [Om]

lemma lt_omega_succ (σ : O) : σ + 1 + 1 < ω_ (σ + 1) := by
  have h1 : σ ≤ ω_ σ := omega_strictMono.le_apply
  have h2 : ω_ σ < ω_ (σ + 1) := omega_lt_omega.2 (lt_add_one σ)
  have hl := isSuccLimit_omega (σ + 1)
  exact hl.add_one_lt (hl.add_one_lt (lt_of_le_of_lt h1 h2))

/-- For `κ ∈ R` some `η < κ` already has `κ ∈ C(α,η)`. -/
theorem exists_base {κ : O} (hκ : κ ∈ Rset) (α : O) : ∃ η < κ, Cl psiK α η κ := by
  rcases hκ with h | ⟨σ, hσ, rfl⟩
  · rw [mem_singleton_iff.1 h]
    exact ⟨0, Iord_pos, Cl.inacc⟩
  · refine ⟨σ + 1 + 1, lt_omega_succ σ, ?_⟩
    have := Cl.om (f := psiK) (α := α) (β := σ + 1 + 1) (Cl.lt (lt_add_one (σ + 1)))
    rwa [Om_succ] at this

/-! ### Lemma 4.5a: totality -/

/-- Least `η` bounding `C(α,β) ∩ κ`. -/
def nextB (κ α β : O) : O := sInf {η | ∀ x, Cl psiK α β x → x < κ → x < η}

theorem nextB_spec {κ : O} (hκ : κ ∈ Rset) (α : O) {β : O} (hβ : β < κ) :
    nextB κ α β < κ ∧ (∀ x, Cl psiK α β x → x < κ → x < nextB κ α β) ∧ β ≤ nextB κ α β := by
  obtain ⟨η, hη, hb⟩ := Cl_bounded (f := psiK) (α := α) hκ hβ
  have hne : {η | ∀ x, Cl psiK α β x → x < κ → x < η}.Nonempty := ⟨η, hb⟩
  have hmem : nextB κ α β ∈ {η | ∀ x, Cl psiK α β x → x < κ → x < η} := csInf_mem hne
  refine ⟨lt_of_le_of_lt (csInf_le' hb) hη, hmem, ?_⟩
  refine le_csInf hne (fun e he => le_of_forall_lt (fun y hy => ?_))
  exact he y (Cl.lt hy) (hy.trans hβ)

def seqB (κ α η0 : O) : ℕ → O
  | 0 => η0
  | n + 1 => nextB κ α (seqB κ α η0 n)

theorem seqB_lt {κ : O} (hκ : κ ∈ Rset) (α : O) {η0 : O} (h0 : η0 < κ) (n : ℕ) :
    seqB κ α η0 n < κ := by
  induction n with
  | zero => exact h0
  | succ n ih => exact (nextB_spec hκ α ih).1

theorem seqB_mono {κ : O} (hκ : κ ∈ Rset) (α : O) {η0 : O} (h0 : η0 < κ) :
    Monotone (seqB κ α η0) :=
  monotone_nat_of_le_succ (fun n => (nextB_spec hκ α (seqB_lt hκ α h0 n)).2.2)

/-- The defining set of `ψ_κ α` has an element below `κ` (Lemma 4.5a, existence). -/
theorem exists_psi_witness {κ : O} (hκ : κ ∈ Rset) (α : O) : ∃ B < κ, B ∈ PsiSet κ α := by
  have hU := Rset_isRU hκ
  obtain ⟨η0, h0, hcl0⟩ := exists_base hκ α
  set b := seqB κ α η0 with hb
  have hlt : ∀ n, b n < κ := seqB_lt hκ α h0
  have hmono : Monotone b := seqB_mono hκ α h0
  have hbdd : BddAbove (range b) := Ordinal.bddAbove_of_small (s := range b)
  set B := ⨆ n, b n with hB
  have hBκ : B < κ := by
    refine Ordinal.lift_iSup_lt_of_lt_cof ?_ hlt
    rw [← Ordinal.lift_cof, hU.cof_eq]
    have := hU.unc
    simpa using this
  have hle : ∀ n, b n ≤ B := fun n => le_ciSup hbdd n
  refine ⟨B, hBκ, hcl0.mono_beta (hle 0), ?_⟩
  intro x hx hxκ
  obtain ⟨η, ⟨n, rfl⟩, hxn⟩ := Cl.sup (f := psiK) (α := α) (β := B) (range b) ⟨b 0, 0, rfl⟩
    (by
      rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
      exact ⟨b (max m n), ⟨_, rfl⟩, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩)
    (fun y hy => by
      obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 hy
      exact ⟨b n, ⟨n, rfl⟩, hn⟩) hx
  have h1 := (nextB_spec hκ α (hlt n)).2.1 x hxn hxκ
  exact lt_of_lt_of_le h1 (hle (n + 1))

theorem psiK_mem {κ : O} (hκ : κ ∈ Rset) (α : O) : psiK κ α ∈ PsiSet κ α := by
  obtain ⟨B, _, hB⟩ := exists_psi_witness hκ α
  rw [psiK_eq_sInf]
  exact csInf_mem ⟨B, hB⟩

/-- Lemma 4.5a (first half): `ψ_κ α < κ` for `κ ∈ R`. -/
theorem psiK_lt {κ : O} (hκ : κ ∈ Rset) (α : O) : psiK κ α < κ := by
  obtain ⟨B, hBκ, hB⟩ := exists_psi_witness hκ α
  rw [psiK_eq_sInf]
  exact lt_of_le_of_lt (csInf_le' hB) hBκ

theorem kappa_mem_Ck {κ : O} (hκ : κ ∈ Rset) (α : O) : κ ∈ Ck κ α := (psiK_mem hκ α).1

/-- Lemma 4.4c: `κ ∈ C(α,κ)`. -/
theorem kappa_mem_C {κ : O} (hκ : κ ∈ Rset) (α : O) : κ ∈ C α κ :=
  Cl.mono_beta (psiK_lt hκ α).le (kappa_mem_Ck hκ α)

/-- Lemma 4.4d: `C_κ(α) ∩ κ = ψ_κ α`. -/
theorem Ck_inter {κ : O} (hκ : κ ∈ Rset) (α : O) : Ck κ α ∩ Iio κ = Iio (psiK κ α) := by
  ext x
  constructor
  · rintro ⟨hx, hxκ⟩
    exact (psiK_mem hκ α).2 x hx hxκ
  · intro hx
    exact ⟨Cl.lt hx, hx.trans (psiK_lt hκ α)⟩

/-- Lemma 4.5a (second half): `ψ_κ α ∉ C_κ(α)`. -/
theorem psiK_not_mem_Ck {κ : O} (hκ : κ ∈ Rset) (α : O) : psiK κ α ∉ Ck κ α := by
  intro h
  have := (Ck_inter hκ α).subset ⟨h, psiK_lt hκ α⟩
  exact lt_irrefl _ (mem_Iio.1 this)

end OrdinalAnalysis.KPi.Ord
