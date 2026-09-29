import OrdinalAnalysis.KPi.Ord.Omega

/-!
# Buchholz 1992, Lemma 4.5 (a)-(i)

(a) `psiK_lt`, `psiK_not_mem_Ck` (in `Psi.lean`);  (b) `psiK_lt_psiK`;
(c) `psiK_ne_zero`, `psiK_ne_Om`, `psiK_veblen_lt`;  (d) `Om_mem_C`;
(e) `nice_C` (Cantor normal form exponents, see `CNF.lean`);
(f) `psi_Om_lt`, `psiK_between`;  (g) `Om_psiI`;  (h) `mem_of_between`;  (i) `psiK_mono`.
-/

set_option autoImplicit false

open Ordinal Cardinal Set Order

noncomputable section

namespace OrdinalAnalysis.KPi.Ord

/-! ### closure of a regular uncountable ordinal -/

lemma IsRU.principal_add {κ : O} (h : IsRU κ) : IsPrincipal (· + ·) κ := by
  have := isPrincipal_add_ord h.unc.le
  rwa [h.ord] at this

lemma IsRU.omega_lt {κ : O} (h : IsRU κ) : (ω : O) < κ := by
  rw [h.lt_iff, Ordinal.card_omega0]; exact h.unc

lemma IsRU.one_lt {κ : O} (h : IsRU κ) : (1 : O) < κ := lt_trans one_lt_omega0 h.omega_lt

/-! ### closure of `ψ_κ α` -/

section psi_closure
variable {κ : O} (hκ : κ ∈ Rset) (α : O)
include hκ

theorem psiK_add_lt {x y : O} (hx : x < psiK κ α) (hy : y < psiK κ α) : x + y < psiK κ α := by
  have hxκ := hx.trans (psiK_lt hκ α)
  have hyκ := hy.trans (psiK_lt hκ α)
  have h : x + y ∈ Ck κ α ∩ Iio κ :=
    ⟨Cl.add (Cl.lt hx) (Cl.lt hy), (Rset_isRU hκ).principal_add hxκ hyκ⟩
  rw [Ck_inter hκ α] at h
  exact h

/-- Lemma 4.5c, second part: `ψ_κ α` is closed under `φ`. -/
theorem psiK_veblen_lt {x y : O} (hx : x < psiK κ α) (hy : y < psiK κ α) :
    veblen x y < psiK κ α := by
  have hxκ := hx.trans (psiK_lt hκ α)
  have hyκ := hy.trans (psiK_lt hκ α)
  have h : veblen x y ∈ Ck κ α ∩ Iio κ :=
    ⟨Cl.phi (Cl.lt hx) (Cl.lt hy), veblen_lt_of_RU (Rset_isRU hκ) x hxκ y hyκ⟩
  rw [Ck_inter hκ α] at h
  exact h

theorem one_lt_psiK : 1 < psiK κ α := by
  have h : (1 : O) ∈ Ck κ α ∩ Iio κ := ⟨Cl.one, (Rset_isRU hκ).one_lt⟩
  rw [Ck_inter hκ α] at h
  exact h

/-- Lemma 4.5c, first part: `ψ_κ α ≠ 0`. -/
theorem psiK_ne_zero : psiK κ α ≠ 0 := by
  intro h
  apply psiK_not_mem_Ck hκ α
  have h0 : Cl psiK α (psiK κ α) 0 := Cl.zero
  rwa [← h] at h0

/-- Lemma 4.5c, first part: `ψ_κ α ∉ {Ω_σ : σ < Ω_σ}`. -/
theorem psiK_ne_Om {σ : O} (hσ : σ < Om σ) : psiK κ α ≠ Om σ := by
  intro h
  apply psiK_not_mem_Ck hκ α
  have hσψ : σ < psiK κ α := by rw [h]; exact hσ
  have hcl : Cl psiK α (psiK κ α) (Om σ) := Cl.om (Cl.lt hσψ)
  rwa [← h] at hcl

theorem psiK_isSuccLimit : IsSuccLimit (psiK κ α) := by
  refine Ordinal.isSuccLimit_iff.2 ⟨psiK_ne_zero hκ α, isSuccPrelimit_of_succ_lt (fun a ha => ?_)⟩
  rw [Order.succ_eq_add_one]
  exact psiK_add_lt hκ α ha (one_lt_psiK hκ α)

theorem opow_psiK : ω ^ psiK κ α = psiK κ α := by
  refine le_antisymm ?_ (right_le_opow _ one_lt_omega0)
  refine (opow_le_of_isSuccLimit omega0_pos.ne' (psiK_isSuccLimit hκ α)).2 (fun b hb => ?_)
  have h0 : (0 : O) < psiK κ α := pos_iff_ne_zero.2 (psiK_ne_zero hκ α)
  have := psiK_veblen_lt hκ α h0 hb
  rw [veblen_zero_apply] at this
  exact this.le

end psi_closure

/-! ### 4.5(b) -/

theorem psiK_lt_psiK {κ α α0 : O} (hκ : κ ∈ Rset) (h : α0 < α) (h0 : α0 ∈ Ck κ α) :
    psiK κ α0 < psiK κ α := by
  have hm : psiK κ α0 ∈ Ck κ α ∩ Iio κ :=
    ⟨Cl.psi h0 (kappa_mem_Ck hκ α) h hκ, psiK_lt hκ α0⟩
  rw [Ck_inter hκ α] at hm
  exact hm

/-! ### 4.5(d): `Ω_σ ∈ C(α,β) → σ ∈ C(α,β)` -/

theorem Om_mem_C {α β σ : O} (h : Om σ ∈ C α β) : σ ∈ C α β := by
  by_contra hσ
  rcases (le_Om σ).eq_or_lt with heq | hlt
  · rw [← heq] at h; exact hσ h
  have hσ0 : σ ≠ 0 := by
    intro h0; subst h0; rw [Om_zero] at hlt; exact lt_irrefl _ hlt
  have hne : ∀ x, Cl psiK α β x → x ≠ Om σ := by
    intro x hx
    induction hx with
    | lt hx =>
      intro heq
      subst heq
      exact hσ (Cl.lt (lt_of_le_of_lt (le_Om σ) hx))
    | zero =>
      intro heq
      have := Om_pos hσ0
      rw [← heq] at this
      exact lt_irrefl _ this
    | inacc =>
      intro heq
      have h1 : σ = Iord := Om_inj.1 (by rw [Om_Iord]; exact heq.symm)
      subst h1
      rw [Om_Iord] at hlt
      exact lt_irrefl _ hlt
    | add hx hy ihx ihy =>
      rename_i x y
      intro heq
      have hx' : x < Om σ := lt_of_le_of_ne (heq ▸ le_self_add) ihx
      have hy' : y < Om σ := lt_of_le_of_ne (heq ▸ le_add_self) ihy
      have h3 : x + y < Om σ := Om_principal_add hσ0 hx' hy'
      rw [heq] at h3
      exact lt_irrefl _ h3
    | phi hx hy ihx ihy =>
      rename_i x y
      intro heq
      have hx' : x < Om σ := lt_of_le_of_ne (heq ▸ left_le_veblen x y) ihx
      have hy' : y < Om σ := lt_of_le_of_ne (heq ▸ right_le_veblen x y) ihy
      have := veblen_lt_Om hσ0 hx' hy'
      rw [heq] at this
      exact lt_irrefl _ this
    | om hx ih =>
      rename_i x
      intro heq
      have : x = σ := Om_inj.1 heq
      subst this
      exact hσ hx
    | psi hξ hπ hξα hπR ih1 ih2 =>
      rename_i ξ π
      intro heq
      exact psiK_ne_Om hπR ξ hlt heq
  exact hne _ h rfl

/-! ### 4.5(e): niceness of `C(α,β)` (Cantor normal form exponents) -/

theorem span_srt (η : O) :
    ∀ l : List O, Srt l → ∃ l₁ l₂, l = l₁ ++ l₂ ∧ (∀ ξ ∈ l₁, η ≤ ξ) ∧ (∀ ξ ∈ l₂, ξ < η) := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[], [], rfl, by simp, by simp⟩
  | cons ξ t ih =>
    intro hs
    have ht : Srt t := (List.pairwise_cons.1 hs).2
    have htb : ∀ b ∈ t, b ≤ ξ := (List.pairwise_cons.1 hs).1
    by_cases h : η ≤ ξ
    · obtain ⟨l₁, l₂, he, h1, h2⟩ := ih ht
      refine ⟨ξ :: l₁, l₂, by simp [he], ?_, h2⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h
      · exact h1 x hx
    · refine ⟨[], ξ :: t, rfl, by simp, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact not_le.1 h
      · exact lt_of_le_of_lt (htb x hx) (not_le.1 h)

/-- Every element of `C(α,β)` has a Cantor normal form all of whose exponents lie in `C(α,β)`. -/
theorem rep_C {α β γ : O} (h : Cl psiK α β γ) :
    ∃ l, Srt l ∧ (∀ ξ ∈ l, Cl psiK α β ξ) ∧ pw l = γ := by
  induction h with
  | lt hx =>
    rename_i x
    obtain ⟨l, hs, hp⟩ := exists_pw x
    refine ⟨l, hs, fun ξ hξ => Cl.lt ?_, hp⟩
    exact lt_of_le_of_lt (hp ▸ le_of_mem_pw hξ) hx
  | zero => exact ⟨[], List.Pairwise.nil, by simp, rfl⟩
  | inacc =>
    refine ⟨[Iord], by simp [Srt], ?_, by simp [opow_Iord]⟩
    intro ξ hξ
    rw [List.mem_singleton.1 hξ]
    exact Cl.inacc
  | add hx hy ihx ihy =>
    rename_i x y
    obtain ⟨l, hls, hlc, hlp⟩ := ihx
    obtain ⟨m, hms, hmc, hmp⟩ := ihy
    cases m with
    | nil =>
      refine ⟨l, hls, hlc, ?_⟩
      rw [← hmp] at *
      simpa using hlp
    | cons η m' =>
      obtain ⟨l₁, l₂, he, h1, h2⟩ := span_srt η l hls
      have hls' : Srt (l₁ ++ l₂) := he ▸ hls
      have hl₁ : Srt l₁ := (List.pairwise_append.1 hls').1
      have habs : pw l₂ + pw (η :: m') = pw (η :: m') := by
        rw [pw_cons]
        exact add_of_omega0_opow_le (pw_lt_of_lt h2) le_self_add
      refine ⟨l₁ ++ η :: m', ?_, ?_, ?_⟩
      · rw [Srt, List.pairwise_append]
        refine ⟨hl₁, hms, ?_⟩
        intro a ha b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact h1 a ha
        · exact ((List.pairwise_cons.1 hms).1 b hb).trans (h1 a ha)
      · intro ξ hξ
        rcases List.mem_append.1 hξ with h | h
        · exact hlc ξ (he ▸ List.mem_append_left _ h)
        · exact hmc ξ h
      · calc pw (l₁ ++ η :: m') = pw l₁ + pw (η :: m') := pw_append _ _
          _ = pw l₁ + (pw l₂ + pw (η :: m')) := by rw [habs]
          _ = (pw l₁ + pw l₂) + pw (η :: m') := (add_assoc _ _ _).symm
          _ = pw l + pw (η :: m') := by rw [← pw_append, ← he]
          _ = x + y := by rw [hlp, hmp]
  | phi hx hy ihx ihy =>
    rename_i x y
    rcases eq_or_ne x 0 with rfl | hx0
    · refine ⟨[y], by simp [Srt], ?_, by simp [veblen_zero_apply]⟩
      intro ξ hξ; rw [List.mem_singleton.1 hξ]; exact hy
    · have h1 : ω ^ veblen x y = veblen x y := by
        have := veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y
        rwa [veblen_zero_apply] at this
      refine ⟨[veblen x y], by simp [Srt], ?_, by simp [h1]⟩
      intro ξ hξ; rw [List.mem_singleton.1 hξ]; exact Cl.phi hx hy
  | om hx ih =>
    rename_i x
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨[], List.Pairwise.nil, by simp, by simp [Om_zero]⟩
    · refine ⟨[Om x], by simp [Srt], ?_, by simp [opow_Om hx0]⟩
      intro ξ hξ; rw [List.mem_singleton.1 hξ]; exact Cl.om hx
  | psi hξ hπ hξα hπR ih1 ih2 =>
    rename_i ξ π
    refine ⟨[psiK π ξ], by simp [Srt], ?_, by simp [opow_psiK hπR ξ]⟩
    intro ζ hζ; rw [List.mem_singleton.1 hζ]; exact Cl.psi hξ hπ hξα hπR

/-- Lemma 4.5e: `ω^{ξ₀} + … + ω^{ξₙ} ∈ C(α,β) ⇔ ξᵢ ∈ C(α,β)` for `ξ₀ ≥ … ≥ ξₙ`
(the natural sum of ω-powers is the sorted ordinary sum). -/
theorem nice_C {α β : O} {l : List O} (hl : Srt l) :
    pw l ∈ C α β ↔ ∀ ξ ∈ l, ξ ∈ C α β := by
  constructor
  · intro h
    obtain ⟨m, hms, hmc, hmp⟩ := rep_C (show Cl psiK α β (pw l) from h)
    have := pw_inj hms hl hmp
    subst this
    exact hmc
  · intro h
    clear hl
    induction l with
    | nil => exact Cl.zero
    | cons ξ t ih =>
      simp only [pw_cons]
      have h1 : Cl psiK α β ξ := h ξ (by simp)
      have h2 : Cl psiK α β (pw t) := ih (fun x hx => h x (by simp [hx]))
      exact Cl.add h1.opow h2

/-- `C(α,β)` is closed under predecessor `σ+1 ↦ σ` (consequence of 4.5e). -/
theorem pred_mem_C {α β σ : O} (h : σ + 1 ∈ C α β) : σ ∈ C α β := by
  obtain ⟨l, hls, hlp⟩ := exists_pw σ
  have hs : Srt (l ++ [0]) := by
    rw [Srt, List.pairwise_append]
    refine ⟨hls, by simp, ?_⟩
    intro a _ b hb
    rw [List.mem_singleton.1 hb]; exact bot_le
  have hp : pw (l ++ [0]) = σ + 1 := by simp [pw_append, hlp]
  rw [← hp] at h
  have h2 := (nice_C hs).1 h
  exact hlp ▸ (nice_C hls).2 (fun ξ hξ => h2 ξ (List.mem_append_left _ hξ))

/-! ### 4.5(f) -/

/-- Lemma 4.5f (lower bound): `Ω_σ < ψ_{Ω_{σ+1}} α`. -/
theorem psi_Om_lt {σ : O} (hσ : σ < Iord) (α : O) : Om σ < psiK (ω_ (σ + 1)) α := by
  have hκ : ω_ (σ + 1) ∈ Rset := omega_succ_mem_Rset hσ
  have h1 : Om (σ + 1) ∈ Ck (ω_ (σ + 1)) α := by rw [Om_succ]; exact kappa_mem_Ck hκ α
  have h2 : σ + 1 ∈ Ck (ω_ (σ + 1)) α := Om_mem_C h1
  have h3 : σ ∈ Ck (ω_ (σ + 1)) α := pred_mem_C h2
  have h4 : Om σ ∈ Ck (ω_ (σ + 1)) α := Cl.om h3
  have h5 : Om σ < ω_ (σ + 1) := by rw [← Om_succ]; exact Om_strictMono (lt_add_one σ)
  have h6 := (Ck_inter hκ α).subset (show Om σ ∈ Ck (ω_ (σ + 1)) α ∩ Iio (ω_ (σ + 1)) from ⟨h4, h5⟩)
  exact mem_Iio.1 h6

/-- Lemma 4.5f: `κ = Ω_{σ+1} → Ω_σ < ψ_κ α < Ω_{σ+1}`. -/
theorem psiK_between {σ : O} (hσ : σ < Iord) (α : O) :
    Om σ < psiK (ω_ (σ + 1)) α ∧ psiK (ω_ (σ + 1)) α < ω_ (σ + 1) :=
  ⟨psi_Om_lt hσ α, psiK_lt (omega_succ_mem_Rset hσ) α⟩

/-! ### 4.5(g) -/

/-- Lemma 4.5g: `Ω_{ψ_I α} = ψ_I α`. -/
theorem Om_psiI (α : O) : Om (psiK Iord α) = psiK Iord α := by
  have hI := Iord_mem_Rset
  set γ := psiK Iord α with hγdef
  have hγI : γ < Iord := psiK_lt hI α
  obtain ⟨σ, h1, h2⟩ := exists_Om_between γ
  have hσI : σ < Iord := lt_of_le_of_lt ((le_Om σ).trans h1) hγI
  have hσ1 : σ + 1 < Iord := isSuccLimit_Iord.add_one_lt hσI
  have hOm : Om (σ + 1) < Iord := Om_lt_Iord hσ1
  have hnot : Om (σ + 1) ∉ Ck Iord α := by
    intro hm
    have := (Ck_inter hI α).subset (show Om (σ + 1) ∈ Ck Iord α ∩ Iio Iord from ⟨hm, hOm⟩)
    exact absurd (mem_Iio.1 this) (not_lt.2 h2.le)
  have hσnot : σ ∉ Ck Iord α := fun h => hnot (Cl.om (Cl.succ h))
  have hle : γ ≤ σ := by
    by_contra hlt
    exact hσnot (Cl.lt (not_le.1 hlt))
  have hσγ : σ = γ := le_antisymm ((le_Om σ).trans h1) hle
  rw [hσγ] at h1
  exact le_antisymm h1 (le_Om γ)

/-! ### 4.5(h) -/

/-- Lemma 4.5h: `Ω_σ ≤ γ ≤ Ω_{σ+1}` and `γ ∈ C(α,β)` imply `σ ∈ C(α,β)`. -/
theorem mem_of_between {α β σ γ : O} (h1 : Om σ ≤ γ) (h2 : γ ≤ Om (σ + 1)) (hγ : γ ∈ C α β) :
    σ ∈ C α β := by
  by_contra hσ
  have hσ0 : σ ≠ 0 := by
    intro h0
    apply hσ
    rw [h0]
    exact Cl.zero
  have hσ1 : ¬ Cl psiK α β (σ + 1) := fun h => hσ (pred_mem_C h)
  have hOmσ : ¬ Cl psiK α β (Om σ) := fun h => hσ (Om_mem_C h)
  have hOmσ1 : ¬ Cl psiK α β (Om (σ + 1)) := fun h => hσ1 (Om_mem_C h)
  have key : ∀ x, Cl psiK α β x → ¬ (Om σ ≤ x ∧ x ≤ Om (σ + 1)) := by
    intro x hx
    induction hx with
    | lt hx =>
      rintro ⟨ha, _⟩
      exact hσ (Cl.lt (lt_of_le_of_lt (le_Om σ) (lt_of_le_of_lt ha hx)))
    | zero =>
      rintro ⟨ha, _⟩
      exact absurd (Om_pos hσ0) (not_lt.2 ha)
    | inacc =>
      rintro ⟨ha, hb⟩
      have ha' : σ ≤ Iord := Om_le_iff.1 (by rw [Om_Iord]; exact ha)
      have hb' : Iord ≤ σ + 1 := Om_le_iff.1 (by rw [Om_Iord]; exact hb)
      rcases hb'.eq_or_lt with h | h
      · exact hσ1 (h ▸ Cl.inacc)
      · have : Iord ≤ σ := Order.lt_add_one_iff.1 h
        have : σ = Iord := le_antisymm ha' this
        exact hσ (this ▸ Cl.inacc)
    | add hx hy ihx ihy =>
      rename_i x y
      rintro ⟨ha, hb⟩
      have hx' : x < Om σ := by
        by_contra hnot
        exact ihx ⟨not_lt.1 hnot, le_self_add.trans hb⟩
      have hy' : y < Om σ := by
        by_contra hnot
        exact ihy ⟨not_lt.1 hnot, le_add_self.trans hb⟩
      have h3 : x + y < Om σ := Om_principal_add hσ0 hx' hy'
      exact absurd ha (not_le.2 h3)
    | phi hx hy ihx ihy =>
      rename_i x y
      rintro ⟨ha, hb⟩
      have hx' : x < Om σ := by
        by_contra hnot
        exact ihx ⟨not_lt.1 hnot, (left_le_veblen x y).trans hb⟩
      have hy' : y < Om σ := by
        by_contra hnot
        exact ihy ⟨not_lt.1 hnot, (right_le_veblen x y).trans hb⟩
      exact absurd ha (not_le.2 (veblen_lt_Om hσ0 hx' hy'))
    | om hx ih =>
      rename_i x
      rintro ⟨ha, hb⟩
      have h1' : σ ≤ x := Om_le_iff.1 ha
      have h2' : x ≤ σ + 1 := Om_le_iff.1 hb
      rcases h2'.eq_or_lt with h | h
      · exact hσ1 (h ▸ hx)
      · have : x ≤ σ := Order.lt_add_one_iff.1 h
        have : x = σ := le_antisymm this h1'
        exact hσ (this ▸ hx)
    | psi hξ hπ hξα hπR ih1 ih2 =>
      rename_i ξ π
      rintro ⟨ha, hb⟩
      have hψ : Cl psiK α β (psiK π ξ) := Cl.psi hξ hπ hξα hπR
      rcases hπR with hI | ⟨τ, hτ, rfl⟩
      · have hπI : π = Iord := mem_singleton_iff.1 hI
        subst hπI
        have ha' : σ ≤ psiK Iord ξ := Om_le_iff.1 (by rw [Om_psiI]; exact ha)
        have hb' : psiK Iord ξ ≤ σ + 1 := Om_le_iff.1 (by rw [Om_psiI]; exact hb)
        rcases hb'.eq_or_lt with h | h
        · exact hσ1 (h ▸ hψ)
        · have : psiK Iord ξ ≤ σ := Order.lt_add_one_iff.1 h
          have : psiK Iord ξ = σ := le_antisymm this ha'
          exact hσ (this ▸ hψ)
      · obtain ⟨hlow, hhigh⟩ := psiK_between hτ ξ
        have hhigh' : psiK (ω_ (τ + 1)) ξ < Om (τ + 1) := by rw [Om_succ]; exact hhigh
        have hσ1' : σ < τ + 1 :=
          Om_lt_iff.1 (lt_of_le_of_lt ha hhigh')
        have hτ1' : τ < σ + 1 := Om_lt_iff.1 (lt_of_lt_of_le hlow hb)
        have hστ : σ = τ := le_antisymm (Order.lt_add_one_iff.1 hσ1') (Order.lt_add_one_iff.1 hτ1')
        subst hστ
        rw [← Om_succ] at hπ
        exact hOmσ1 hπ
  exact key γ hγ ⟨h1, h2⟩

/-! ### 4.5(i) -/

/-- Lemma 4.5i: `α₀ ≤ α → ψ_κ α₀ ≤ ψ_κ α ∧ C_κ(α₀) ⊆ C_κ(α)`. -/
theorem psiK_mono {κ α α0 : O} (hκ : κ ∈ Rset) (h : α0 ≤ α) :
    psiK κ α0 ≤ psiK κ α ∧ Ck κ α0 ⊆ Ck κ α := by
  have hκC : Cl psiK α0 (psiK κ α) κ := by
    rcases id hκ with hI | ⟨σ, hσ, rfl⟩
    · rw [mem_singleton_iff.1 hI]; exact Cl.inacc
    · have h1 : Om σ < psiK (ω_ (σ + 1)) α := psi_Om_lt hσ α
      have h2 : σ < psiK (ω_ (σ + 1)) α := lt_of_le_of_lt (le_Om σ) h1
      have h3 := Cl.om (f := psiK) (α := α0) (Cl.succ (Cl.lt h2))
      rwa [Om_succ] at h3
  have hsub : ∀ x, Cl psiK α0 (psiK κ α) x → x < κ → x < psiK κ α := by
    intro x hx hxκ
    have hx' : Cl psiK α (psiK κ α) x := hx.mono_alpha h
    have := (Ck_inter hκ α).subset (show x ∈ Ck κ α ∩ Iio κ from ⟨hx', hxκ⟩)
    exact mem_Iio.1 this
  have hψ : psiK κ α ∈ PsiSet κ α0 := ⟨hκC, hsub⟩
  have hle : psiK κ α0 ≤ psiK κ α := by
    rw [psiK_eq_sInf]; exact csInf_le' hψ
  exact ⟨hle, fun x hx => (Cl.mono_beta hle hx).mono_alpha h⟩

end OrdinalAnalysis.KPi.Ord
