import OrdinalAnalysis.KPi.Ord.Psi
import OrdinalAnalysis.KPi.Ord.CNF

/-!
# Facts about `Ω_σ` and `I`; closure of `ψ_κ α` under `+`, `φ`, `ω^`

Elementary properties of `Om` (Def 4.1), `Iord`, and the existence of the interval `[Ω_σ, Ω_{σ+1})`
containing a given ordinal.  `veblen_lt_Om` shows that every `Ω_σ` (`σ ≠ 0`) is closed under `φ`, even when `ℵ_σ`
is singular, via a regular successor cardinal below it.  These are the ingredients of Lemma 4.5 (c), (d), (g), (h).
-/

set_option autoImplicit false

open Ordinal Cardinal Set Order

noncomputable section

namespace OrdinalAnalysis.KPi.Ord

/-! ### `Om` -/

lemma Om_zero : Om 0 = 0 := by simp [Om]

lemma Om_of_ne {σ : O} (h : σ ≠ 0) : Om σ = ω_ σ := by simp [Om, h]

lemma Om_strictMono : StrictMono Om := by
  intro a b hab
  have hb : b ≠ 0 := (lt_of_le_of_lt (bot_le : (⊥ : O) ≤ a) hab).ne'
  rw [Om_of_ne hb]
  by_cases ha : a = 0
  · subst ha; rw [Om_zero]; exact omega_pos b
  · rw [Om_of_ne ha]; exact omega_lt_omega.2 hab

lemma le_Om (σ : O) : σ ≤ Om σ := Om_strictMono.le_apply

lemma Om_le_iff {a b : O} : Om a ≤ Om b ↔ a ≤ b := Om_strictMono.le_iff_le
lemma Om_lt_iff {a b : O} : Om a < Om b ↔ a < b := Om_strictMono.lt_iff_lt
lemma Om_inj {a b : O} : Om a = Om b ↔ a = b := Om_strictMono.injective.eq_iff

lemma Om_pos {σ : O} (h : σ ≠ 0) : 0 < Om σ := by
  rw [Om_of_ne h]; exact omega_pos σ

lemma Om_eq_ord {σ : O} (h : σ ≠ 0) : Om σ = (ℵ_ σ).ord := by
  rw [Om_of_ne h, Cardinal.ord_aleph]

lemma Om_principal_add {σ : O} (h : σ ≠ 0) : IsPrincipal (· + ·) (Om σ) := by
  rw [Om_eq_ord h]; exact isPrincipal_add_ord (Cardinal.aleph0_le_aleph σ)

lemma Om_principal_opow {σ : O} (h : σ ≠ 0) : IsPrincipal (· ^ ·) (Om σ) := by
  rw [Om_eq_ord h]; exact isPrincipal_opow_ord (Cardinal.aleph0_le_aleph σ)

lemma omega_lt_Om {σ : O} (h : σ ≠ 0) : ω < Om σ := by
  rw [Om_of_ne h, ← omega_zero]
  exact omega_lt_omega.2 (pos_iff_ne_zero.2 h)

lemma isSuccLimit_Om {σ : O} (h : σ ≠ 0) : IsSuccLimit (Om σ) := by
  rw [Om_of_ne h]; exact isSuccLimit_omega σ

lemma opow_Om {σ : O} (h : σ ≠ 0) : ω ^ Om σ = Om σ := by
  refine le_antisymm ?_ (right_le_opow _ one_lt_omega0)
  refine (opow_le_of_isSuccLimit omega0_pos.ne' (isSuccLimit_Om h)).2 (fun b hb => ?_)
  exact (Om_principal_opow h (omega_lt_Om h) hb).le

/-- A regular successor cardinal is a regular uncountable initial ordinal. -/
lemma isRU_ord_succ {c : Cardinal.{1}} (hc : ℵ₀ ≤ c) : IsRU (Order.succ c).ord := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Cardinal.card_ord]; exact Cardinal.isRegular_succ hc
  · rw [Cardinal.card_ord]
  · rw [Cardinal.card_ord]; exact lt_of_le_of_lt hc (Order.lt_succ c)

/-- Every `Ω_σ` (`σ ≠ 0`) is closed under `φ`, even when `ℵ_σ` is singular: below any `x, y < Ω_σ`
there is a regular successor cardinal `≤ Ω_σ`. -/
lemma veblen_lt_Om {σ : O} (hσ : σ ≠ 0) {x y : O} (hx : x < Om σ) (hy : y < Om σ) :
    veblen x y < Om σ := by
  set c : Cardinal.{1} := max ℵ₀ (max x y).card with hc
  have hU : IsRU (Order.succ c).ord := isRU_ord_succ (le_max_left _ _)
  have hlt : max x y < Om σ := max_lt hx hy
  rw [Om_eq_ord hσ] at hlt ⊢
  have hcl : c < ℵ_ σ := by
    refine max_lt ?_ (Cardinal.lt_ord.1 hlt)
    rw [← Cardinal.aleph_zero]
    exact Cardinal.aleph_lt_aleph.2 (pos_iff_ne_zero.2 hσ)
  have hle : (Order.succ c).ord ≤ (ℵ_ σ).ord := Cardinal.ord_le_ord.2 (Order.succ_le_of_lt hcl)
  have hxy : max x y < (Order.succ c).ord := by
    rw [Cardinal.lt_ord]
    exact lt_of_le_of_lt (le_max_right _ _) (Order.lt_succ c)
  exact lt_of_lt_of_le
    (veblen_lt_of_RU hU x (lt_of_le_of_lt (le_max_left _ _) hxy) y
      (lt_of_le_of_lt (le_max_right _ _) hxy)) hle

/-! ### `Iord` -/

lemma Iord_ne_zero : Iord ≠ 0 := Iord_pos.ne'

lemma Om_Iord : Om Iord = Iord := by rw [Om_of_ne Iord_ne_zero]; exact Iord_spec.2

lemma isSuccLimit_Iord : IsSuccLimit Iord := by
  have := isSuccLimit_Om Iord_ne_zero
  rwa [Om_Iord] at this

lemma opow_Iord : ω ^ Iord = Iord := by
  have := opow_Om Iord_ne_zero
  rwa [Om_Iord] at this

/-- `ω_ ` values below `Iord` are below `Iord`. -/
lemma Om_lt_Iord {σ : O} (h : σ < Iord) : Om σ < Iord := by
  have := Om_strictMono h
  rwa [Om_Iord] at this

/-! ### Every ordinal lies in some `[Ω_σ, Ω_{σ+1})` -/

theorem exists_Om_between (γ : O) : ∃ σ, Om σ ≤ γ ∧ γ < Om (σ + 1) := by
  have hne : {σ : O | γ < Om σ}.Nonempty := ⟨γ + 1, lt_of_lt_of_le (lt_add_one γ) (le_Om _)⟩
  set τ := sInf {σ : O | γ < Om σ} with hτdef
  have hτ : γ < Om τ := csInf_mem hne
  have hmin : ∀ σ < τ, Om σ ≤ γ := by
    intro σ hσ
    by_contra hlt
    exact absurd (csInf_le' (show σ ∈ {σ : O | γ < Om σ} from not_le.1 hlt)) (not_le.2 hσ)
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h, Om_zero] at hτ; exact not_lt_zero hτ
  rcases zero_or_succ_or_isSuccLimit τ with h | ⟨σ, hσ⟩ | hl
  · exact absurd h hτ0
  · have hσ' : σ + 1 = τ := (Order.succ_eq_add_one σ).symm.trans hσ
    refine ⟨σ, hmin σ (by rw [← hσ']; exact lt_add_one σ), ?_⟩
    rw [hσ']; exact hτ
  · exfalso
    have hτ' : Om τ ≤ γ := by
      rw [Om_of_ne hτ0]
      rw [(isNormal_omega).apply_of_isSuccLimit hl]
      refine ciSup_le' (fun b => ?_)
      have hb : b.1 + 1 < τ := hl.add_one_lt b.2
      have := hmin (b.1 + 1) hb
      rw [Om_succ] at this
      exact (omega_le_omega.2 (lt_add_one b.1).le).trans this
    exact absurd hτ (not_lt.2 hτ')

end OrdinalAnalysis.KPi.Ord
