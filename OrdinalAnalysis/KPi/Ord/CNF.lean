import Mathlib

/-!
# Sums of `ω`-powers: Cantor normal forms as sorted lists

Mathlib has no natural (Hessenberg) sum on `Ordinal`, so B92's `ω^{α₀} # … # ω^{αₙ}` (Def 3.5, Lemma 4.5 (e))
is rendered as the ordinary sum `ω^{ξ₀} + … + ω^{ξₙ}` over a weakly decreasing list `[ξ₀ ≥ … ≥ ξₙ]`
(the natural sum of `ω`-powers is exactly this sorted ordinary sum).  We prove existence (`exists_pw`)
and uniqueness (`pw_inj`) of this representation.
-/

set_option autoImplicit false

open Ordinal

noncomputable section

namespace OrdinalAnalysis.KPi.Ord

universe u

/-- `pw [ξ₀,…,ξₙ] = ω^ξ₀ + … + ω^ξₙ`. -/
def pw : List Ordinal.{u} → Ordinal.{u}
  | [] => 0
  | ξ :: l => ω ^ ξ + pw l

/-- Decreasing lists (weakly). -/
abbrev Srt (l : List Ordinal.{u}) : Prop := l.Pairwise (fun a b => b ≤ a)

@[simp] theorem pw_nil : pw ([] : List Ordinal.{u}) = 0 := rfl
@[simp] theorem pw_cons (ξ : Ordinal.{u}) (l : List Ordinal.{u}) : pw (ξ :: l) = ω ^ ξ + pw l := rfl

theorem pw_append (l m : List Ordinal.{u}) : pw (l ++ m) = pw l + pw m := by
  induction l with
  | nil => simp
  | cons ξ l ih => simp [ih, add_assoc]

theorem pw_lt_of_lt {l : List Ordinal.{u}} {e : Ordinal.{u}} (h : ∀ ξ ∈ l, ξ < e) : pw l < ω ^ e := by
  induction l with
  | nil => simpa using opow_pos e omega0_pos
  | cons ξ l ih =>
    simp only [pw_cons]
    have h1 : ω ^ ξ < ω ^ e := (opow_lt_opow_iff_right one_lt_omega0).2 (h ξ (by simp))
    have h2 : pw l < ω ^ e := ih (fun x hx => h x (by simp [hx]))
    exact isPrincipal_add_omega0_opow e h1 h2

theorem le_pw {l : List Ordinal.{u}} {ξ : Ordinal.{u}} (h : ξ ∈ l) : ω ^ ξ ≤ pw l := by
  induction l with
  | nil => simp at h
  | cons η l ih =>
    simp only [pw_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_self_add
    · exact (ih h).trans (le_add_self)

theorem le_of_mem_pw {l : List Ordinal.{u}} {ξ : Ordinal.{u}} (h : ξ ∈ l) : ξ ≤ pw l :=
  (right_le_opow ξ one_lt_omega0).trans (le_pw h)

theorem pw_pos {l : List Ordinal.{u}} (h : l ≠ []) : 0 < pw l := by
  cases l with
  | nil => exact absurd rfl h
  | cons ξ l => simp only [pw_cons]; exact lt_of_lt_of_le (opow_pos ξ omega0_pos) le_self_add

theorem pw_eq_zero {l : List Ordinal.{u}} (h : pw l = 0) : l = [] := by
  by_contra hne
  exact (pw_pos hne).ne' h

/-- Uniqueness of the Cantor normal form. -/
theorem pw_inj : ∀ {l m : List Ordinal.{u}}, Srt l → Srt m → pw l = pw m → l = m := by
  intro l
  induction l with
  | nil =>
    intro m _ _ h
    exact (pw_eq_zero h.symm).symm
  | cons ξ l ih =>
    intro m hl hm h
    cases m with
    | nil => exact absurd (pw_eq_zero h) (by simp)
    | cons η m =>
      have hl' : Srt l := (List.pairwise_cons.1 hl).2
      have hm' : Srt m := (List.pairwise_cons.1 hm).2
      have hlb : ∀ b ∈ l, b ≤ ξ := (List.pairwise_cons.1 hl).1
      have hmb : ∀ b ∈ m, b ≤ η := (List.pairwise_cons.1 hm).1
      simp only [pw_cons] at h
      have key : ∀ {ξ η : Ordinal.{u}} {l m : List Ordinal.{u}}, (∀ b ∈ l, b ≤ ξ) → ξ < η →
          ω ^ ξ + pw l ≠ ω ^ η + pw m := by
        intro ξ η l m hlb hlt heq
        have h1 : ω ^ ξ + pw l < ω ^ (ξ + 1) :=
          pw_lt_of_lt (l := ξ :: l) (fun x hx => by
            rcases List.mem_cons.1 hx with rfl | hx
            · exact lt_add_one _
            · exact lt_of_le_of_lt (hlb x hx) (lt_add_one _)) |> fun h => by simpa using h
        have h2 : ω ^ (ξ + 1) ≤ ω ^ η :=
          (opow_le_opow_iff_right one_lt_omega0).2 (Order.add_one_le_iff.2 hlt)
        exact absurd heq (ne_of_lt (lt_of_lt_of_le h1 (h2.trans le_self_add)))
      rcases lt_trichotomy ξ η with hlt | rfl | hgt
      · exact absurd h (key hlb hlt)
      · have : pw l = pw m := add_left_cancel h
        rw [ih hl' hm' this]
      · exact absurd h.symm (key hmb hgt)

/-- Existence of the Cantor normal form (as a decreasing list of exponents). -/
theorem exists_pw : ∀ γ : Ordinal.{u}, ∃ l, Srt l ∧ pw l = γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | _ γ IH =>
    rcases eq_or_ne γ 0 with rfl | hγ
    · exact ⟨[], List.Pairwise.nil, rfl⟩
    · set e := log ω γ with he
      have hle : ω ^ e ≤ γ := opow_log_le_self ω hγ
      have hlt : γ < ω ^ (e + 1) := by
        have := lt_opow_succ_log_self (b := ω) one_lt_omega0 γ
        simpa [Order.succ_eq_add_one] using this
      have hpos : ω ^ e ≠ 0 := (opow_pos e omega0_pos).ne'
      set q := γ / ω ^ e with hq
      set r := γ % ω ^ e with hr
      have hqr : ω ^ e * q + r = γ := div_add_mod γ (ω ^ e)
      have hqω : q < ω := by
        rw [hq, ← Ordinal.lt_mul_iff_div_lt hpos]
        rwa [← opow_succ, Order.succ_eq_add_one]
      have hq0 : 0 < q := (Ordinal.div_pos hpos).2 hle
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 hqω
      have hrlt : r < ω ^ e := mod_lt γ hpos
      have hrγ : r < γ := lt_of_lt_of_le hrlt hle
      obtain ⟨l', hl's, hl'⟩ := IH r hrγ
      have hl'lt : ∀ ξ ∈ l', ξ < e := by
        intro ξ hξ
        have := (le_pw hξ).trans_lt (hl' ▸ hrlt)
        exact (opow_lt_opow_iff_right one_lt_omega0).1 this
      have hrep : ∀ k : ℕ, pw (List.replicate k e) = ω ^ e * (k : Ordinal.{u}) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [List.replicate_succ, pw_cons, ih]
          have : ((k + 1 : ℕ) : Ordinal.{u}) = 1 + (k : Ordinal.{u}) := by
            push_cast; exact Nat.cast_add_one_comm k
          rw [this, mul_add, mul_one]
      refine ⟨List.replicate n e ++ l', ?_, ?_⟩
      · rw [Srt, List.pairwise_append]
        refine ⟨?_, hl's, ?_⟩
        · rw [List.pairwise_replicate]; exact Or.inr le_rfl
        · intro a ha b hb
          rw [List.eq_of_mem_replicate ha]
          exact (hl'lt b hb).le
      · rw [pw_append, hrep, hl', ← hn, hqr]

end OrdinalAnalysis.KPi.Ord
