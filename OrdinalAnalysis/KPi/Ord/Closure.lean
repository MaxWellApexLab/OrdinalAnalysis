import OrdinalAnalysis.KPi.Ord.Veblen

/-!
# Buchholz 1992, Def 4.2: the closure `C(α, β)`, Lemma 4.4 (a), (b)

`Cl f α β x` says that `x` lies in the closure of `β ∪ {0, I}` under `+`, `φ = veblen`, `σ ↦ Ω_σ` and
`(ξ, π) ↦ f π ξ` for `ξ < α`, `π ∈ R`.  The function `f` is a parameter (later `f = ψ`), so the
cardinality bound `#C(α, β) ≤ max ℵ₀ |β|` is proved once and for all, uniformly in `f`.

* `Cl.of_limit`  : Lemma 4.4 (b), `C(α, β) = ⋃_{η<β} C(α, η)` for limit `β`;
* `card_Cl_lt`   : Lemma 4.4 (a), `π ∈ R`, `β < π` imply `#C(α, β) < π`;
* `Cl_bounded`   : `C(α, β) ∩ π` is bounded in `π` (used for the totality of `ψ`).
-/

set_option autoImplicit false

open Ordinal Cardinal Set Order

noncomputable section

namespace OrdinalAnalysis.KPi.Ord

/-- B92 Def 4.2: the closure of `β ∪ {0, I}` under `+`, `φ`, `σ ↦ Ω_σ`, `(ξ, π) ↦ ψ_π ξ` (`ξ<α`, `π∈R`),
with `ψ_π ξ` given by the parameter `f π ξ`. -/
inductive Cl (f : O → O → O) (α β : O) : O → Prop
  | lt {x : O} : x < β → Cl f α β x
  | zero : Cl f α β 0
  | inacc : Cl f α β Iord
  | add {x y : O} : Cl f α β x → Cl f α β y → Cl f α β (x + y)
  | phi {x y : O} : Cl f α β x → Cl f α β y → Cl f α β (veblen x y)
  | om {x : O} : Cl f α β x → Cl f α β (Om x)
  | psi {ξ π : O} : Cl f α β ξ → Cl f α β π → ξ < α → π ∈ Rset → Cl f α β (f π ξ)

section basic
variable {f g : O → O → O} {α α' β β' x : O}

theorem Cl.mono_beta (h : β ≤ β') : Cl f α β x → Cl f α β' x := by
  intro hx
  induction hx with
  | lt hx => exact Cl.lt (hx.trans_le h)
  | zero => exact Cl.zero
  | inacc => exact Cl.inacc
  | add _ _ h1 h2 => exact Cl.add h1 h2
  | phi _ _ h1 h2 => exact Cl.phi h1 h2
  | om _ h1 => exact Cl.om h1
  | psi _ _ hξ hπ h1 h2 => exact Cl.psi h1 h2 hξ hπ

theorem Cl.mono_alpha (h : α ≤ α') : Cl f α β x → Cl f α' β x := by
  intro hx
  induction hx with
  | lt hx => exact Cl.lt hx
  | zero => exact Cl.zero
  | inacc => exact Cl.inacc
  | add _ _ h1 h2 => exact Cl.add h1 h2
  | phi _ _ h1 h2 => exact Cl.phi h1 h2
  | om _ h1 => exact Cl.om h1
  | psi _ _ hξ hπ h1 h2 => exact Cl.psi h1 h2 (hξ.trans_le h) hπ

/-- Only the values `f π ξ` with `ξ < α` matter. -/
theorem Cl.congr (h : ∀ ξ < α, ∀ π, f π ξ = g π ξ) : Cl f α β x → Cl g α β x := by
  intro hx
  induction hx with
  | lt hx => exact Cl.lt hx
  | zero => exact Cl.zero
  | inacc => exact Cl.inacc
  | add _ _ h1 h2 => exact Cl.add h1 h2
  | phi _ _ h1 h2 => exact Cl.phi h1 h2
  | om _ h1 => exact Cl.om h1
  | psi _ _ hξ hπ h1 h2 => rw [h _ hξ]; exact Cl.psi h1 h2 hξ hπ

theorem Cl.one : Cl f α β 1 := by
  have := Cl.phi (f := f) (α := α) (β := β) Cl.zero Cl.zero
  simpa using this

theorem Cl.succ (hx : Cl f α β x) : Cl f α β (x + 1) := Cl.add hx Cl.one

theorem Cl.opow (hx : Cl f α β x) : Cl f α β (ω ^ x) := by
  have := Cl.phi (f := f) (α := α) (β := β) Cl.zero hx
  simpa using this

/-- If `β` is approximated from below by a directed family `D`, every element of `Cl f α β` already
lies in some `Cl f α η`, `η ∈ D`. -/
theorem Cl.sup (D : Set O) (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (hβ : ∀ y, y < β → ∃ η ∈ D, y < η) :
    Cl f α β x → ∃ η ∈ D, Cl f α η x := by
  intro hx
  induction hx with
  | lt hx => obtain ⟨η, hη, h⟩ := hβ _ hx; exact ⟨η, hη, Cl.lt h⟩
  | zero => obtain ⟨η, hη⟩ := hne; exact ⟨η, hη, Cl.zero⟩
  | inacc => obtain ⟨η, hη⟩ := hne; exact ⟨η, hη, Cl.inacc⟩
  | add _ _ h1 h2 =>
    obtain ⟨a, ha, h1⟩ := h1
    obtain ⟨b, hb, h2⟩ := h2
    obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
    exact ⟨c, hc, Cl.add (h1.mono_beta hac) (h2.mono_beta hbc)⟩
  | phi _ _ h1 h2 =>
    obtain ⟨a, ha, h1⟩ := h1
    obtain ⟨b, hb, h2⟩ := h2
    obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
    exact ⟨c, hc, Cl.phi (h1.mono_beta hac) (h2.mono_beta hbc)⟩
  | om _ h1 =>
    obtain ⟨a, ha, h1⟩ := h1
    exact ⟨a, ha, Cl.om h1⟩
  | psi _ _ hξ hπ h1 h2 =>
    obtain ⟨a, ha, h1⟩ := h1
    obtain ⟨b, hb, h2⟩ := h2
    obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
    exact ⟨c, hc, Cl.psi (h1.mono_beta hac) (h2.mono_beta hbc) hξ hπ⟩

/-- Lemma 4.4b: `C(α,β) = ⋃_{η<β} C(α,η)` for limit `β`. -/
theorem Cl.of_limit (hβ : IsSuccLimit β) (hx : Cl f α β x) : ∃ η < β, Cl f α η x := by
  have hne : (Iio β).Nonempty := ⟨0, hβ.bot_lt⟩
  have hdir : DirectedOn (· ≤ ·) (Iio β) := by
    intro a ha b hb
    exact ⟨max a b, mem_Iio.2 (max_lt (mem_Iio.1 ha) (mem_Iio.1 hb)), le_max_left _ _, le_max_right _ _⟩
  obtain ⟨η, hη, h⟩ := Cl.sup (Iio β) hne hdir (fun y hy => ⟨y + 1, hβ.add_one_lt hy, lt_add_one y⟩) hx
  exact ⟨η, hη, h⟩

end basic

/-! ### Cardinality: `#C(α,β) ≤ max ℵ₀ |β|` -/

section card
variable (f : O → O → O) (α β : O)

/-- One closure step. -/
def Stp (S : Set O) : Set O :=
  S ∪ {0, Iord} ∪ image2 (· + ·) S S ∪ image2 veblen S S ∪ Om '' S ∪
    image2 (fun ξ π => f π ξ) (S ∩ Iio α) (S ∩ Rset)

theorem subset_Stp (S : Set O) : S ⊆ Stp f α S := by
  intro x hx
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hx))))

private theorem card_union_le {X Y : Set O} {m : Cardinal.{2}} (hm : ℵ₀ ≤ m)
    (hX : #X ≤ m) (hY : #Y ≤ m) : #(X ∪ Y : Set O) ≤ m :=
  (Cardinal.mk_union_le X Y).trans ((add_le_add hX hY).trans (by rw [Cardinal.add_eq_self hm]))

theorem card_Stp_le (S : Set O) : #(Stp f α S) ≤ max ℵ₀ #S := by
  have hm : ℵ₀ ≤ max ℵ₀ #S := le_max_left _ _
  have hS : #S ≤ max ℵ₀ #S := le_max_right _ _
  have hmul : #S * #S ≤ max ℵ₀ #S := by
    refine (Cardinal.mul_le_max _ _).trans ?_
    rw [max_self, max_comm]
  have hfin : #({0, Iord} : Set O) ≤ max ℵ₀ #S :=
    ((Set.toFinite _).lt_aleph0).le.trans hm
  unfold Stp
  refine card_union_le hm (card_union_le hm (card_union_le hm (card_union_le hm
    (card_union_le hm hS hfin) ?_) ?_) (Cardinal.mk_image_le.trans hS)) ?_
  · exact Cardinal.mk_image2_le.trans hmul
  · exact Cardinal.mk_image2_le.trans hmul
  · refine Cardinal.mk_image2_le.trans (le_trans ?_ hmul)
    exact mul_le_mul' (Cardinal.mk_le_mk_of_subset inter_subset_left)
      (Cardinal.mk_le_mk_of_subset inter_subset_left)

/-- The stages. -/
def Tn : ℕ → Set O
  | 0 => Iio β
  | n + 1 => Stp f α (Tn n)

theorem Tn_mono : Monotone (Tn f α β) :=
  monotone_nat_of_le_succ (fun n => subset_Stp f α (Tn f α β n))

theorem card_Tn (n : ℕ) : #(Tn f α β n) ≤ max ℵ₀ (Cardinal.lift.{2, 1} β.card) := by
  induction n with
  | zero =>
    simp only [Tn]
    rw [Cardinal.mk_Iio_ordinal]
    exact le_max_right _ _
  | succ n ih =>
    refine (card_Stp_le f α _).trans ?_
    exact max_le (le_max_left _ _) ih

theorem Cl.exists_stage {x : O} (hx : Cl f α β x) : ∃ n, x ∈ Tn f α β n := by
  induction hx with
  | lt hx => exact ⟨0, hx⟩
  | zero => exact ⟨1, Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl)))))⟩
  | inacc => exact ⟨1, Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl)))))⟩
  | add _ _ h1 h2 =>
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    refine ⟨max a b + 1, Or.inl (Or.inl (Or.inl (Or.inr ?_)))⟩
    exact ⟨_, Tn_mono f α β (le_max_left a b) ha, _, Tn_mono f α β (le_max_right a b) hb, rfl⟩
  | phi _ _ h1 h2 =>
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    refine ⟨max a b + 1, Or.inl (Or.inl (Or.inr ?_))⟩
    exact ⟨_, Tn_mono f α β (le_max_left a b) ha, _, Tn_mono f α β (le_max_right a b) hb, rfl⟩
  | om _ h1 =>
    obtain ⟨a, ha⟩ := h1
    exact ⟨a + 1, Or.inl (Or.inr ⟨_, ha, rfl⟩)⟩
  | psi _ _ hξ hπ h1 h2 =>
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    refine ⟨max a b + 1, Or.inr ?_⟩
    exact ⟨_, ⟨Tn_mono f α β (le_max_left a b) ha, hξ⟩, _,
      ⟨Tn_mono f α β (le_max_right a b) hb, hπ⟩, rfl⟩

/-- `#C(α,β) ≤ max ℵ₀ |β|` (in `Cardinal.{2}`). -/
theorem card_Cl_le : #{x | Cl f α β x} ≤ max ℵ₀ (Cardinal.lift.{2, 1} β.card) := by
  refine Cardinal.mk_le_of_countable_eventually_mem
    (f := fun n => {x : {x | Cl f α β x} | x.1 ∈ Tn f α β n}) (l := Filter.atTop) ?_ ?_
  · intro x
    obtain ⟨n, hn⟩ := Cl.exists_stage f α β x.2
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact Tn_mono f α β hm hn
  · intro n
    refine le_trans ?_ (card_Tn f α β n)
    refine Cardinal.mk_le_of_injective (f := fun y => (⟨y.1.1, y.2⟩ : Tn f α β n)) ?_
    intro a b h
    have h' : a.1.1 = b.1.1 := congrArg (fun z : ↥(Tn f α β n) => z.1) h
    exact Subtype.ext (Subtype.ext h')

end card

/-- Lemma 4.4a: for `π ∈ R` and `β < π`, `#C(α,β) < π`. -/
theorem card_Cl_lt {f : O → O → O} {α β π : O} (hπ : π ∈ Rset) (hβ : β < π) :
    #{x | Cl f α β x} < Cardinal.lift.{2, 1} π.card := by
  have hU := Rset_isRU hπ
  refine lt_of_le_of_lt (card_Cl_le f α β) (max_lt ?_ ?_)
  · rw [← Cardinal.lift_aleph0.{2, 1}]; exact Cardinal.lift_lt.2 hU.unc
  · exact Cardinal.lift_lt.2 ((hU.lt_iff).1 hβ)

/-- Boundedness below a regular `π ∈ R`: `C(α,β) ∩ π` is bounded in `π` when `β < π`. -/
theorem Cl_bounded {f : O → O → O} {α β π : O} (hπ : π ∈ Rset) (hβ : β < π) :
    ∃ η < π, ∀ x, Cl f α β x → x < π → x < η := by
  have hU := Rset_isRU hπ
  set S : Set O := {x | Cl f α β x} ∩ Iio π with hS
  have hSc : #S < Cardinal.lift.{2, 1} π.cof := by
    rw [hU.cof_eq]
    exact lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset inter_subset_left) (card_Cl_lt hπ hβ)
  have hsm : Small.{1} S := small_subset (inter_subset_right (s := {x | Cl f α β x}) (t := Iio π))
  have h1 : (⨆ i : S, (i.1 + 1)) < π :=
    Ordinal.lift_iSup_add_one_lt_of_lt_cof (f := fun i : S => i.1) (a := π)
      (by rw [← Ordinal.lift_cof]; rwa [Cardinal.lift_id'.{1, 2}]) (fun i => i.2.2)
  refine ⟨⨆ i : S, (i.1 + 1), h1, fun x hx hxπ => ?_⟩
  have : x + 1 ≤ ⨆ i : S, (i.1 + 1) :=
    le_ciSup (f := fun i : S => i.1 + 1) (Ordinal.bddAbove_of_small (s := range fun i : S => i.1 + 1))
      ⟨x, hx, hxπ⟩
  exact lt_of_lt_of_le (lt_add_one x) this

end OrdinalAnalysis.KPi.Ord
