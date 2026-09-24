/-
  Structural tools for building derivations of the generalised descent.

  * **∨-inversion** (`OmegaDerivableR.invOr`): from `⊢^α_ρ (φ ⋎ ψ) :: Γ` derive
    `⊢^α_ρ φ :: ψ :: Γ`, at the same height and the same rank.  Proved in the
    `⊆`-form `invOrSub`, by induction on the derivation, exactly as
    `OmegaDerivableR.invAllSub` proves ∀-inversion: the only rule that can
    introduce `φ ⋎ ψ` as a principal formula is `or`, and there the premise is
    already the inverted sequent; every other rule is rebuilt around the
    inverted premises.
-/
import OrdinalAnalysis.Ramified.InfTools

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder

/-- Close a goal `l₁ ⊆ l₂` between explicit lists. -/
macro "subset_tac" : tactic =>
  `(tactic| (intro x hx; simp only [List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hx ⊢; tauto))

namespace OmegaDerivableR

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals LRA} {I : InstantiationR} {ρ : Gamma0Note}

/-- **∨-inversion, `⊆`-form.**  If a sequent all of whose formulas lie in
`(φ₀ ⋎ ψ₀) :: Ξ` is derivable at height `α`, then so is `φ₀ :: ψ₀ :: Ξ`. -/
theorem invOrSub {α : O} {Θ : Sequent LRA} (h : OmegaDerivableR A I ρ α Θ) :
    ∀ {φ₀ ψ₀ : Proposition LRA} {Ξ : Sequent LRA}, Θ ⊆ (φ₀ ⋎ ψ₀) :: Ξ →
      OmegaDerivableR A I ρ α (φ₀ :: ψ₀ :: Ξ) := by
  induction h with
  | @atom α φ hAT =>
      intro φ₀ ψ₀ Ξ hsub
      have hhead : φ ∈ (φ₀ ⋎ ψ₀) :: Ξ := hsub (show φ ∈ [φ] by simp)
      rcases List.mem_cons.mp hhead with heq | hΞ
      · exact absurd heq (Literals.ne_or hAT)
      · exact .contraction (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; simp [hΞ]) (.atom hAT)
  | @identity α k rl v =>
      intro φ₀ ψ₀ Ξ hsub
      have hrel : Semiformula.rel rl v ∈ (φ₀ ⋎ ψ₀) :: Ξ :=
        hsub (show Semiformula.rel rl v ∈ [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
      have hnrel : Semiformula.nrel rl v ∈ (φ₀ ⋎ ψ₀) :: Ξ :=
        hsub (show Semiformula.nrel rl v ∈ [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
      rcases List.mem_cons.mp hrel with heq | hΞ1
      · exact absurd heq (ne_of_headTag (by simp only [headTag_rel, headTag_or]; decide))
      rcases List.mem_cons.mp hnrel with heq | hΞ2
      · exact absurd heq (ne_of_headTag (by simp only [headTag_nrel, headTag_or]; decide))
      refine .contraction (fun x hx => ?_) (.identity rl v)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [List.mem_cons]
      rcases hx with rfl | rfl
      · tauto
      · tauto
  | @verum α =>
      intro φ₀ ψ₀ Ξ hsub
      have hhead : (⊤ : Proposition LRA) ∈ (φ₀ ⋎ ψ₀) :: Ξ :=
        hsub (show (⊤ : Proposition LRA) ∈ [⊤] by simp)
      rcases List.mem_cons.mp hhead with heq | hΞ
      · exact absurd heq (ne_of_headTag (by simp only [headTag_verum, headTag_or]; decide))
      · exact .contraction (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; simp [hΞ]) .verum
  | @or α β φ ψ Γ hlt hprem ih =>
      intro φ₀ ψ₀ Ξ hsub
      have hΓ : Γ ⊆ (φ₀ ⋎ ψ₀) :: Ξ := fun x hx => hsub (List.mem_cons_of_mem _ hx)
      have hsub' : (φ :: ψ :: Γ) ⊆ (φ₀ ⋎ ψ₀) :: (φ :: ψ :: Ξ) := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · simp
        · simp
        · rcases List.mem_cons.mp (hΓ hx) with rfl | hx
          · simp
          · simp [hx]
      have hstep := ih hsub'
      by_cases heq : φ = φ₀ ∧ ψ = ψ₀
      · obtain ⟨rfl, rfl⟩ := heq
        exact (OmegaDerivableR.contraction (by subset_tac) hstep).mono_ord (le_of_lt hlt)
      · have hX : (φ ⋎ ψ) ∈ Ξ := by
          have hhead : (φ ⋎ ψ) ∈ (φ₀ ⋎ ψ₀) :: Ξ := hsub (show (φ⋎ψ) ∈ (φ⋎ψ)::Γ by simp)
          rcases List.mem_cons.mp hhead with he | hΞ
          · exact absurd (by simpa using he) heq
          · exact hΞ
        have hprem' : OmegaDerivableR A I ρ β (φ :: ψ :: φ₀ :: ψ₀ :: Ξ) :=
          .contraction (by subset_tac) hstep
        have hconcl : OmegaDerivableR A I ρ α ((φ ⋎ ψ) :: φ₀ :: ψ₀ :: Ξ) := .or hlt hprem'
        exact .contraction (fun x hx => by
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | rfl | rfl | hx
          · exact Or.inr (Or.inr hX)
          · tauto
          · tauto
          · tauto) hconcl
  | @and α β γ φ ψ Γ h1 h2 d1 d2 ih1 ih2 =>
      intro φ₀ ψ₀ Ξ hsub
      have hX : (φ ⋏ ψ) ∈ Ξ := by
        have hhead : (φ ⋏ ψ) ∈ (φ₀ ⋎ ψ₀) :: Ξ := hsub (show (φ⋏ψ) ∈ (φ⋏ψ)::Γ by simp)
        rcases List.mem_cons.mp hhead with heq | hΞ
        · exact absurd heq (ne_of_headTag (by simp only [headTag_and, headTag_or]; decide))
        · exact hΞ
      have hΓ : Γ ⊆ (φ₀ ⋎ ψ₀) :: Ξ := fun x hx => hsub (List.mem_cons_of_mem _ hx)
      have hsub1 : (φ :: Γ) ⊆ (φ₀ ⋎ ψ₀) :: (φ :: Ξ) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases List.mem_cons.mp (hΓ hx) with rfl | hx
          · simp
          · simp [hx]
      have hsub2 : (ψ :: Γ) ⊆ (φ₀ ⋎ ψ₀) :: (ψ :: Ξ) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases List.mem_cons.mp (hΓ hx) with rfl | hx
          · simp
          · simp [hx]
      have hconcl : OmegaDerivableR A I ρ α ((φ ⋏ ψ) :: φ₀ :: ψ₀ :: Ξ) :=
        .and h1 h2 (.contraction (by subset_tac) (ih1 hsub1))
          (.contraction (by subset_tac) (ih2 hsub2))
      exact .contraction (fun x hx => by
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | rfl | rfl | hx
        · exact Or.inr (Or.inr hX)
        · tauto
        · tauto
        · tauto) hconcl
  | @omegaRule α φ Γ β hf hprem ih =>
      intro φ₀ ψ₀ Ξ hsub
      have hX : (∀¹ φ : Proposition LRA) ∈ Ξ := by
        have hhead : (∀¹ φ : Proposition LRA) ∈ (φ₀ ⋎ ψ₀) :: Ξ :=
          hsub (show (∀¹ φ : Proposition LRA) ∈ (∀¹ φ)::Γ by simp)
        rcases List.mem_cons.mp hhead with heq | hΞ
        · exact absurd heq (ne_of_headTag (by simp only [headTag_all, headTag_or]; decide))
        · exact hΞ
      have hΓ : Γ ⊆ (φ₀ ⋎ ψ₀) :: Ξ := fun x hx => hsub (List.mem_cons_of_mem _ hx)
      have hfam : ∀ m : ℕ, OmegaDerivableR A I ρ (β m) (I.inst φ m :: φ₀ :: ψ₀ :: Ξ) := by
        intro m
        have hsubm : (I.inst φ m :: Γ) ⊆ (φ₀ ⋎ ψ₀) :: (I.inst φ m :: Ξ) := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · simp
          · rcases List.mem_cons.mp (hΓ hx) with rfl | hx
            · simp
            · simp [hx]
        exact .contraction (by subset_tac) (ih m hsubm)
      have hconcl : OmegaDerivableR A I ρ α ((∀¹ φ) :: φ₀ :: ψ₀ :: Ξ) := .omegaRule β hf hfam
      exact .contraction (fun x hx => by
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | rfl | rfl | hx
        · exact Or.inr (Or.inr hX)
        · tauto
        · tauto
        · tauto) hconcl
  | @exs α β φ Γ nc hlt hprem ih =>
      intro φ₀ ψ₀ Ξ hsub
      have hX : (∃¹ φ) ∈ Ξ := by
        have hhead : (∃¹ φ) ∈ (φ₀ ⋎ ψ₀) :: Ξ := hsub (show (∃¹ φ) ∈ (∃¹ φ)::Γ by simp)
        rcases List.mem_cons.mp hhead with heq | hΞ
        · exact absurd heq (ne_of_headTag (by simp only [headTag_exs, headTag_or]; decide))
        · exact hΞ
      have hΓ : Γ ⊆ (φ₀ ⋎ ψ₀) :: Ξ := fun x hx => hsub (List.mem_cons_of_mem _ hx)
      have hsub' : (I.inst φ nc :: Γ) ⊆ (φ₀ ⋎ ψ₀) :: (I.inst φ nc :: Ξ) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases List.mem_cons.mp (hΓ hx) with rfl | hx
          · simp
          · simp [hx]
      have hconcl : OmegaDerivableR A I ρ α ((∃¹ φ) :: φ₀ :: ψ₀ :: Ξ) :=
        .exs nc hlt (.contraction (by subset_tac) (ih hsub'))
      exact .contraction (fun x hx => by
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | rfl | rfl | hx
        · exact Or.inr (Or.inr hX)
        · tauto
        · tauto
        · tauto) hconcl
  | @contraction α Δ Γc hsubc hd ih =>
      intro φ₀ ψ₀ Ξ hsub
      exact ih (fun x hx => hsub (hsubc hx))
  | @cut α β γ φ Γc Δc hrk h1 h2 d1 d2 ih1 ih2 =>
      intro φ₀ ψ₀ Ξ hsub
      have hΓc : Γc ⊆ (φ₀ ⋎ ψ₀) :: Ξ := fun x hx => hsub (List.mem_append.mpr (Or.inl hx))
      have hΔc : Δc ⊆ (φ₀ ⋎ ψ₀) :: Ξ := fun x hx => hsub (List.mem_append.mpr (Or.inr hx))
      have hsub1 : (φ :: Γc) ⊆ (φ₀ ⋎ ψ₀) :: (φ :: Ξ) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases List.mem_cons.mp (hΓc hx) with rfl | hx
          · simp
          · simp [hx]
      have hsub2 : (∼φ :: Δc) ⊆ (φ₀ ⋎ ψ₀) :: (∼φ :: Ξ) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases List.mem_cons.mp (hΔc hx) with rfl | hx
          · simp
          · simp [hx]
      have hconcl : OmegaDerivableR A I ρ α ((φ₀ :: ψ₀ :: Ξ) ++ (φ₀ :: ψ₀ :: Ξ)) :=
        .cut hrk h1 h2 (.contraction (by subset_tac) (ih1 hsub1))
          (.contraction (by subset_tac) (ih2 hsub2))
      exact .contraction (by subset_tac) hconcl
  | @pr α β a nc Γc ha hlt hprem ih =>
      intro φ₀ ψ₀ Ξ hsub
      have hX : memAt (lvl a) (I.num nc) (I.num a) ∈ Ξ := by
        have hhead : memAt (lvl a) (I.num nc) (I.num a) ∈ (φ₀ ⋎ ψ₀) :: Ξ :=
          hsub (show memAt (lvl a) (I.num nc) (I.num a) ∈
            memAt (lvl a) (I.num nc) (I.num a) :: Γc by simp)
        rcases List.mem_cons.mp hhead with heq | hΞ
        · exact absurd heq (ne_of_headTag (by simp only [headTag_memAt, headTag_or]; decide))
        · exact hΞ
      have hΓc : Γc ⊆ (φ₀ ⋎ ψ₀) :: Ξ := fun x hx => hsub (List.mem_cons_of_mem _ hx)
      have hsub' : (I.inst (body a) nc :: Γc) ⊆ (φ₀ ⋎ ψ₀) :: (I.inst (body a) nc :: Ξ) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases List.mem_cons.mp (hΓc hx) with rfl | hx
          · simp
          · simp [hx]
      have hconcl : OmegaDerivableR A I ρ α
          (memAt (lvl a) (I.num nc) (I.num a) :: φ₀ :: ψ₀ :: Ξ) :=
        .pr ha hlt (.contraction (by subset_tac) (ih hsub'))
      exact .contraction (fun x hx => by
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | rfl | rfl | hx
        · exact Or.inr (Or.inr hX)
        · tauto
        · tauto
        · tauto) hconcl
  | @npr α β a nc Γc ha hlt hprem ih =>
      intro φ₀ ψ₀ Ξ hsub
      have hX : nmemAt (lvl a) (I.num nc) (I.num a) ∈ Ξ := by
        have hhead : nmemAt (lvl a) (I.num nc) (I.num a) ∈ (φ₀ ⋎ ψ₀) :: Ξ :=
          hsub (show nmemAt (lvl a) (I.num nc) (I.num a) ∈
            nmemAt (lvl a) (I.num nc) (I.num a) :: Γc by simp)
        rcases List.mem_cons.mp hhead with heq | hΞ
        · exact absurd heq (ne_of_headTag (by simp only [headTag_nmemAt, headTag_or]; decide))
        · exact hΞ
      have hΓc : Γc ⊆ (φ₀ ⋎ ψ₀) :: Ξ := fun x hx => hsub (List.mem_cons_of_mem _ hx)
      have hsub' : (∼(I.inst (body a) nc) :: Γc) ⊆
          (φ₀ ⋎ ψ₀) :: (∼(I.inst (body a) nc) :: Ξ) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases List.mem_cons.mp (hΓc hx) with rfl | hx
          · simp
          · simp [hx]
      have hconcl : OmegaDerivableR A I ρ α
          (nmemAt (lvl a) (I.num nc) (I.num a) :: φ₀ :: ψ₀ :: Ξ) :=
        .npr ha hlt (.contraction (fun x hx => by
          rcases List.mem_cons.mp hx with h1 | hx
          · rw [h1]; exact List.mem_cons_of_mem _ List.mem_cons_self
          rcases List.mem_cons.mp hx with h1 | hx
          · rw [h1]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
          rcases List.mem_cons.mp hx with h1 | hx
          · rw [h1]; exact List.mem_cons_self
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
          (ih hsub'))
      exact .contraction (fun x hx => by
        rcases List.mem_cons.mp hx with h1 | hx
        · rw [h1]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hX)
        · exact hx) hconcl

/-- **∨-inversion.** -/
theorem invOr {α : O} {φ ψ : Proposition LRA} {Γ : Sequent LRA}
    (h : OmegaDerivableR A I ρ α ((φ ⋎ ψ) :: Γ)) : OmegaDerivableR A I ρ α (φ :: ψ :: Γ) :=
  invOrSub h (fun _ hx => hx)

end OmegaDerivableR

end Ramified

end OrdinalAnalysis
