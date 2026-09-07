/-
  The reduction lemma for the infinitary calculus.

  The architecture is the one the finitary version arrived at, and for the same
  reasons: both sequents are related to the target by `⊆`, because contraction
  is subset-based; the recursion is on the symmetric measure `β ⊕ γ`, because
  the quantifier cases produce their second cut premise by running the reduction
  with the two sides swapped; and the ordinal delivered is the natural sum
  doubled, because the propositional cases perform two nested cuts and the plain
  sum leaves room for only one.

  What is different is the quantifier case, and the difference is the whole
  point of moving to this calculus.  In the finitary system the universal rule
  introduces a free variable and the existential rule an arbitrary term, so
  lining the two sides up needs a substitution lemma, and the shift the
  universal rule performs on its context has to be pushed through everything.
  Here both quantifier rules speak about numerals: the existential side names an
  `n`, and the `n`-th premise of the ω-rule is already exactly what the cut
  wants.  No substitution, no shift, no inversion.

  Every case except `contraction` draws on the induction hypothesis for the
  measure, handing it the *whole* left derivation rather than a premise;
  `contraction` cannot, because it leaves the ordinal unchanged, so it is the
  one case that uses the structural hypothesis.
-/
import OrdinalAnalysis.Omega.Calculus

namespace OrdinalAnalysis

open LO LO.FirstOrder LO.FirstOrder.Derivation

variable {L : Language}
variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

namespace OmegaDerivable

/-- The reduction lemma's statement below a bound on the symmetric measure,
packaged so the principal cases can take it as an argument. -/
def RedIHΩ (L : Language) (A : Literals L) (I : Instantiation L) (r : ℕ) (s : O) : Prop :=
  ∀ (β γ : O), OrdinalNotation.nadd β γ < s →
    ∀ {Γ₀ : Sequent L}, OmegaDerivable A I r β Γ₀ →
      ∀ {φ : Proposition L}, φ.complexity ≤ r →
      ∀ {Θ Δ₀ : Sequent L}, Γ₀ ⊆ φ :: Θ →
        OmegaDerivable A I r γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ →
          OmegaDerivable A I r (OrdinalNotation.redOrd β γ) Θ

variable {A : Literals L} {I : Instantiation L}

set_option maxHeartbeats 2000000 in
/-- Principal case for `⋎`. -/
private theorem reduction_or {r : ℕ} {s α α₀ : O}
    (ih2 : RedIHΩ L A I r s) (hα₀ : α₀ < α) :
    ∀ {δ : O} {Δ₀ : Sequent L}, OmegaDerivable A I r δ Δ₀ →
      OrdinalNotation.nadd α δ ≤ s →
      ∀ {χ ρ : Proposition L} {Γ₁ Θ : Sequent L},
        (χ ⋎ ρ).complexity ≤ r →
        OmegaDerivable A I r α₀ (χ :: ρ :: Γ₁) →
        Γ₁ ⊆ (χ ⋎ ρ) :: Θ →
        Δ₀ ⊆ ∼(χ ⋎ ρ) :: Θ →
          OmegaDerivable A I r (OrdinalNotation.redOrd α δ) Θ := by
  intro δ Δ₀ he
  induction he with
  | @atom δ' φ hφT =>
      intro _ χ ρ Γ₁ Θ _ _ _ hssR
      have h := hssR List.mem_cons_self
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact absurd h (Literals.ne_and (ψ₁ := ∼χ) (ψ₂ := ∼ρ) hφT)
      · refine OmegaDerivable.contraction ?_ (OmegaDerivable.atom hφT)
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rw [hx]; exact h
  | @identity δ' k rl v =>
      intro _ χ ρ Γ₁ Θ _ _ _ hssR
      refine of_mem_identity rl v ?_ ?_
      · have h := hssR (show Semiformula.rel rl v ∈
          [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      · have h := hssR (show Semiformula.nrel rl v ∈
          [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
  | @verum δ' =>
      intro _ χ ρ Γ₁ Θ _ _ _ hssR
      refine of_mem_verum ?_
      have h := hssR (show (⊤ : Proposition L) ∈ [(⊤ : Proposition L)] by simp)
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact absurd h (by simp)
      · exact h
  | @contraction δ' Δ' Δ ss _ ih =>
      intro hs χ ρ Γ₁ Θ hr hprem hssL hssR
      exact ih hs hr hprem hssL (fun x hx => hssR (ss hx))
  | @or δ' δ₀ ψ₁ ψ₂ Δ₁ hlt heP _ =>
      intro hs χ ρ Γ₁ Θ hr hprem hssL hssR
      have hmem : (ψ₁ ⋎ ψ₂) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
        (OmegaDerivable.or hα₀ hprem) hr (Θ := ψ₁ :: ψ₂ :: Θ)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssL hx
            simp only [List.mem_cons] at this
            tauto)
        heP
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · rcases hx with rfl | hx
            · tauto
            · have := hssR (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto)
      exact drop_head (OmegaDerivable.or (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @and δ' δ₀ δ₁ ψ₁ ψ₂ Δ₁ hlt₀ hlt₁ heP heQ _ _ =>
      intro hs χ ρ Γ₁ Θ hr hprem hssL hssR
      have hd : OmegaDerivable A I r α ((χ ⋎ ρ) :: Γ₁) := OmegaDerivable.or hα₀ hprem
      have hsubL : ∀ ζ : Proposition L, ((χ ⋎ ρ) :: Γ₁) ⊆ (χ ⋎ ρ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssL hx
          simp only [List.mem_cons] at this
          tauto
      by_cases hcase : (ψ₁ ⋏ ψ₂) = ∼(χ ⋎ ρ)
      ·
        -- PRINCIPAL
        have heq : (ψ₁ ⋏ ψ₂) = ((∼χ) ⋏ (∼ρ)) := hcase
        obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp heq
        have hcχ : χ.complexity < r := by
          simp only [Semiformula.complexity_or] at hr; omega
        have hcρ : ρ.complexity < r := by
          simp only [Semiformula.complexity_or] at hr; omega
        have hA : OmegaDerivable A I r (OrdinalNotation.redOrd α₀ δ') (χ :: ρ :: Θ) :=
          ih2 α₀ δ' (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ' hα₀) hs) hprem hr
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · rcases hx with rfl | hx
                · tauto
                · have := hssL hx
                  simp only [List.mem_cons] at this
                  tauto)
            (OmegaDerivable.and hlt₀ hlt₁ heP heQ)
            (by
              intro x hx
              have := hssR hx
              simp only [List.mem_cons] at this ⊢
              tauto)
        have hB : OmegaDerivable A I r (OrdinalNotation.redOrd α δ₀) ((∼χ) :: Θ) :=
          ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs) hd hr
            (hsubL (∼χ)) heP
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hssR (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
        have hC : OmegaDerivable A I r (OrdinalNotation.redOrd α δ₁) ((∼ρ) :: Θ) :=
          ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs) hd hr
            (hsubL (∼ρ)) heQ
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hssR (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
        have h₀ : OrdinalNotation.nadd α₀ δ' < OrdinalNotation.nadd α δ' :=
          OrdinalNotation.nadd_lt_nadd_left δ' hα₀
        have h₁ : OrdinalNotation.nadd α δ₁ < OrdinalNotation.nadd α δ' :=
          OrdinalNotation.nadd_lt_nadd_right α hlt₁
        have hA' : OmegaDerivable A I r (OrdinalNotation.redOrd α₀ δ') (ρ :: χ :: Θ) := by
          refine OmegaDerivable.contraction ?_ hA
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          tauto
        have step : OmegaDerivable A I r
            (OrdinalNotation.mid (OrdinalNotation.nadd α₀ δ') (OrdinalNotation.nadd α δ₁) (OrdinalNotation.nadd α δ'))
            (χ :: Θ) := by
          refine OmegaDerivable.contraction ?_
            (OmegaDerivable.cut hcρ (OrdinalNotation.sq_lt_mid_left h₀ h₁)
              (OrdinalNotation.sq_lt_mid_right h₀ h₁) hA' hC)
          intro x hx
          simp only [List.cons_append, List.mem_cons, List.mem_append] at hx ⊢
          tauto
        refine OmegaDerivable.contraction ?_
          (OmegaDerivable.cut hcχ (OrdinalNotation.mid_lt_sq h₀ h₁)
            (OrdinalNotation.redOrd_lt_right α hlt₀) step hB)
        intro x hx
        simp only [List.mem_append] at hx
        tauto
      · have hmem : (ψ₁ ⋏ ψ₂) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have hsubR : ∀ ζ : Proposition L, ζ :: Δ₁ ⊆ ∼(χ ⋎ ρ) :: ζ :: Θ := by
          intro ζ x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto
        have kp := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs)
          hd hr (Θ := ψ₁ :: Θ) (hsubL ψ₁) heP (hsubR ψ₁)
        have kq := ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs)
          hd hr (Θ := ψ₂ :: Θ) (hsubL ψ₂) heQ (hsubR ψ₂)
        exact drop_head
          (OmegaDerivable.and (OrdinalNotation.redOrd_lt_right α hlt₀)
            (OrdinalNotation.redOrd_lt_right α hlt₁) kp kq) hmem
  | @omegaRule δ' ψ Δ₁ f hf heP _ =>
      intro hs χ ρ Γ₁ Θ hr hprem hssL hssR
      have hd : OmegaDerivable A I r α ((χ ⋎ ρ) :: Γ₁) := OmegaDerivable.or hα₀ hprem
      have hmem : (∀¹ ψ) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      refine drop_head
        (OmegaDerivable.omegaRule (fun n => OrdinalNotation.redOrd α (f n))
          (fun n => OrdinalNotation.redOrd_lt_right α (hf n)) (fun n => ?_)) hmem
      exact ih2 α (f n) (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α (hf n)) hs)
        hd hr (Θ := I.inst ψ n :: Θ)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssL hx
            simp only [List.mem_cons] at this
            tauto)
        (heP n)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto)
  | @exs δ' δ₀ ψ Δ₁ n hlt heP _ =>
      intro hs χ ρ Γ₁ Θ hr hprem hssL hssR
      have hd : OmegaDerivable A I r α ((χ ⋎ ρ) :: Γ₁) := OmegaDerivable.or hα₀ hprem
      have hmem : (∃¹ ψ) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
        hd hr (Θ := I.inst ψ n :: Θ)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssL hx
            simp only [List.mem_cons] at this
            tauto)
        heP
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto)
      exact drop_head (OmegaDerivable.exs n (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @cut δ' δ₀ δ₁ ψ Δ₁ Δ₂ hc hlt₀ hlt₁ hpp hnn _ _ =>
      intro hs χ ρ Γ₁ Θ hr hprem hssL hssR
      have hd : OmegaDerivable A I r α ((χ ⋎ ρ) :: Γ₁) := OmegaDerivable.or hα₀ hprem
      have hsubL : ∀ ζ : Proposition L, ((χ ⋎ ρ) :: Γ₁) ⊆ (χ ⋎ ρ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssL hx
          simp only [List.mem_cons] at this
          tauto
      have kp := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs)
        hd hr (Θ := ψ :: Θ) (hsubL ψ) hpp
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_left _ hx)
            simp only [List.mem_cons] at this
            tauto)
      have kn := ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs)
        hd hr (Θ := ∼ψ :: Θ) (hsubL (∼ψ)) hnn
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_right _ hx)
            simp only [List.mem_cons] at this
            tauto)
      refine OmegaDerivable.contraction ?_
        (OmegaDerivable.cut hc (OrdinalNotation.redOrd_lt_right α hlt₀)
          (OrdinalNotation.redOrd_lt_right α hlt₁) kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto

set_option maxHeartbeats 2000000 in
/-- Principal case for `⋏`. -/
private theorem reduction_and {r : ℕ} {s α α₀ α₁ : O}
    (ih2 : RedIHΩ L A I r s) (hα₀ : α₀ < α) (hα₁ : α₁ < α) :
    ∀ {δ : O} {Δ₀ : Sequent L}, OmegaDerivable A I r δ Δ₀ →
      OrdinalNotation.nadd α δ ≤ s →
      ∀ {χ ρ : Proposition L} {Γ₁ Θ : Sequent L},
        (χ ⋏ ρ).complexity ≤ r →
        OmegaDerivable A I r α₀ (χ :: Γ₁) →
        OmegaDerivable A I r α₁ (ρ :: Γ₁) →
        Γ₁ ⊆ (χ ⋏ ρ) :: Θ →
        Δ₀ ⊆ ∼(χ ⋏ ρ) :: Θ →
          OmegaDerivable A I r (OrdinalNotation.redOrd α δ) Θ := by
  intro δ Δ₀ he
  induction he with
  | @atom δ' φ hφT =>
      intro _ χ ρ Γ₁ Θ _ _ _ _ hssR
      have h := hssR List.mem_cons_self
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact absurd h (Literals.ne_or (ψ₁ := ∼χ) (ψ₂ := ∼ρ) hφT)
      · refine OmegaDerivable.contraction ?_ (OmegaDerivable.atom hφT)
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rw [hx]; exact h
  | @identity δ' k rl v =>
      intro _ χ ρ Γ₁ Θ _ _ _ _ hssR
      refine of_mem_identity rl v ?_ ?_
      · have h := hssR (show Semiformula.rel rl v ∈
          [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      · have h := hssR (show Semiformula.nrel rl v ∈
          [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
  | @verum δ' =>
      intro _ χ ρ Γ₁ Θ _ _ _ _ hssR
      refine of_mem_verum ?_
      have h := hssR (show (⊤ : Proposition L) ∈ [(⊤ : Proposition L)] by simp)
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact absurd h (by simp)
      · exact h
  | @contraction δ' Δ' Δ ss _ ih =>
      intro hs χ ρ Γ₁ Θ hr hp hq hssL hssR
      exact ih hs hr hp hq hssL (fun x hx => hssR (ss hx))
  | @or δ' δ₀ ψ₁ ψ₂ Δ₁ hlt heP _ =>
      intro hs χ ρ Γ₁ Θ hr hp hq hssL hssR
      have hd : OmegaDerivable A I r α ((χ ⋏ ρ) :: Γ₁) :=
        OmegaDerivable.and hα₀ hα₁ hp hq
      have hsubL : ∀ ζ : Proposition L, ((χ ⋏ ρ) :: Γ₁) ⊆ (χ ⋏ ρ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssL hx
          simp only [List.mem_cons] at this
          tauto
      by_cases hcase : (ψ₁ ⋎ ψ₂) = ∼(χ ⋏ ρ)
      ·
        have heq : (ψ₁ ⋎ ψ₂) = ((∼χ) ⋎ (∼ρ)) := hcase
        obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp heq
        have hcχ : χ.complexity < r := by
          simp only [Semiformula.complexity_and] at hr; omega
        have hcρ : ρ.complexity < r := by
          simp only [Semiformula.complexity_and] at hr; omega
        have hsubR : ∀ ζ : Proposition L,
            (((∼χ) ⋎ (∼ρ)) :: Δ₁) ⊆ ∼(χ ⋏ ρ) :: ζ :: Θ := by
          intro ζ x hx
          have := hssR hx
          simp only [List.mem_cons] at this ⊢
          tauto
        have hsL : (χ :: Γ₁) ⊆ (χ ⋏ ρ) :: χ :: Θ := by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssL hx
            simp only [List.mem_cons] at this
            tauto
        have hsL' : (ρ :: Γ₁) ⊆ (χ ⋏ ρ) :: ρ :: Θ := by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssL hx
            simp only [List.mem_cons] at this
            tauto
        have hA₀ : OmegaDerivable A I r (OrdinalNotation.redOrd α₀ δ') (χ :: Θ) :=
          ih2 α₀ δ' (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ' hα₀) hs) hp hr
            hsL (OmegaDerivable.or hlt heP) (hsubR χ)
        have hA₁ : OmegaDerivable A I r (OrdinalNotation.redOrd α₁ δ') (ρ :: Θ) :=
          ih2 α₁ δ' (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ' hα₁) hs) hq hr
            hsL' (OmegaDerivable.or hlt heP) (hsubR ρ)
        have hB : OmegaDerivable A I r (OrdinalNotation.redOrd α δ₀) ((∼χ) :: (∼ρ) :: Θ) :=
          ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs) hd hr
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hssL hx
                simp only [List.mem_cons] at this
                tauto)
            heP
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · rcases hx with rfl | hx
                · tauto
                · have := hssR (List.mem_cons_of_mem _ hx)
                  simp only [List.mem_cons] at this
                  tauto)
        have h₀ : OrdinalNotation.nadd α₀ δ' < OrdinalNotation.nadd α δ' :=
          OrdinalNotation.nadd_lt_nadd_left δ' hα₀
        have hBs : OrdinalNotation.nadd α δ₀ < OrdinalNotation.nadd α δ' :=
          OrdinalNotation.nadd_lt_nadd_right α hlt
        have step : OmegaDerivable A I r
            (OrdinalNotation.mid (OrdinalNotation.nadd α₀ δ') (OrdinalNotation.nadd α δ₀) (OrdinalNotation.nadd α δ'))
            ((∼ρ) :: Θ) := by
          refine OmegaDerivable.contraction ?_
            (OmegaDerivable.cut hcχ (OrdinalNotation.sq_lt_mid_left h₀ hBs)
              (OrdinalNotation.sq_lt_mid_right h₀ hBs) hA₀ hB)
          intro x hx
          simp only [List.mem_append, List.mem_cons] at hx ⊢
          tauto
        refine OmegaDerivable.contraction ?_
          (OmegaDerivable.cut hcρ (OrdinalNotation.redOrd_lt_left δ' hα₁)
            (OrdinalNotation.mid_lt_sq h₀ hBs) hA₁ step)
        intro x hx
        simp only [List.mem_append] at hx
        tauto
      · have hmem : (ψ₁ ⋎ ψ₂) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
          hd hr (Θ := ψ₁ :: ψ₂ :: Θ) (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hssL hx
              simp only [List.mem_cons] at this
              tauto)
          heP
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · rcases hx with rfl | hx
              · tauto
              · have := hssR (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
        exact drop_head (OmegaDerivable.or (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @and δ' δ₀ δ₁ ψ₁ ψ₂ Δ₁ hlt₀ hlt₁ heP heQ _ _ =>
      intro hs χ ρ Γ₁ Θ hr hp hq hssL hssR
      have hd : OmegaDerivable A I r α ((χ ⋏ ρ) :: Γ₁) :=
        OmegaDerivable.and hα₀ hα₁ hp hq
      have hsubL : ∀ ζ : Proposition L, ((χ ⋏ ρ) :: Γ₁) ⊆ (χ ⋏ ρ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssL hx
          simp only [List.mem_cons] at this
          tauto
      have hmem : (ψ₁ ⋏ ψ₂) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have hsubR : ∀ ζ : Proposition L, ζ :: Δ₁ ⊆ ∼(χ ⋏ ρ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssR (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto
      have kp := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs)
        hd hr (Θ := ψ₁ :: Θ) (hsubL ψ₁) heP (hsubR ψ₁)
      have kq := ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs)
        hd hr (Θ := ψ₂ :: Θ) (hsubL ψ₂) heQ (hsubR ψ₂)
      exact drop_head
        (OmegaDerivable.and (OrdinalNotation.redOrd_lt_right α hlt₀)
          (OrdinalNotation.redOrd_lt_right α hlt₁) kp kq) hmem
  | @omegaRule δ' ψ Δ₁ f hf heP _ =>
      intro hs χ ρ Γ₁ Θ hr hp hq hssL hssR
      have hd : OmegaDerivable A I r α ((χ ⋏ ρ) :: Γ₁) :=
        OmegaDerivable.and hα₀ hα₁ hp hq
      have hmem : (∀¹ ψ) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      refine drop_head
        (OmegaDerivable.omegaRule (fun n => OrdinalNotation.redOrd α (f n))
          (fun n => OrdinalNotation.redOrd_lt_right α (hf n)) (fun n => ?_)) hmem
      exact ih2 α (f n) (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α (hf n)) hs)
        hd hr (Θ := I.inst ψ n :: Θ)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssL hx
            simp only [List.mem_cons] at this
            tauto)
        (heP n)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto)
  | @exs δ' δ₀ ψ Δ₁ n hlt heP _ =>
      intro hs χ ρ Γ₁ Θ hr hp hq hssL hssR
      have hd : OmegaDerivable A I r α ((χ ⋏ ρ) :: Γ₁) :=
        OmegaDerivable.and hα₀ hα₁ hp hq
      have hmem : (∃¹ ψ) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
        hd hr (Θ := I.inst ψ n :: Θ)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssL hx
            simp only [List.mem_cons] at this
            tauto)
        heP
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto)
      exact drop_head (OmegaDerivable.exs n (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @cut δ' δ₀ δ₁ ψ Δ₁ Δ₂ hc hlt₀ hlt₁ hpp hnn _ _ =>
      intro hs χ ρ Γ₁ Θ hr hp hq hssL hssR
      have hd : OmegaDerivable A I r α ((χ ⋏ ρ) :: Γ₁) :=
        OmegaDerivable.and hα₀ hα₁ hp hq
      have hsubL : ∀ ζ : Proposition L, ((χ ⋏ ρ) :: Γ₁) ⊆ (χ ⋏ ρ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssL hx
          simp only [List.mem_cons] at this
          tauto
      have kp := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs)
        hd hr (Θ := ψ :: Θ) (hsubL ψ) hpp
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_left _ hx)
            simp only [List.mem_cons] at this
            tauto)
      have kn := ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs)
        hd hr (Θ := ∼ψ :: Θ) (hsubL (∼ψ)) hnn
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_right _ hx)
            simp only [List.mem_cons] at this
            tauto)
      refine OmegaDerivable.contraction ?_
        (OmegaDerivable.cut hc (OrdinalNotation.redOrd_lt_right α hlt₀)
          (OrdinalNotation.redOrd_lt_right α hlt₁) kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto

set_option maxHeartbeats 2000000 in
/-- Principal case for the ω-rule.

The existential side names an `n`; the ω-rule's `n`-th premise is already the
formula the cut wants.  One cut, no substitution lemma, and no room problem —
the two premises land below `α ⊕ δ` on the nose. -/
private theorem reduction_omega {r : ℕ} {s α : O}
    (ih2 : RedIHΩ L A I r s) :
    ∀ {δ : O} {Δ₀ : Sequent L}, OmegaDerivable A I r δ Δ₀ →
      OrdinalNotation.nadd α δ ≤ s →
      ∀ {χ : Semiproposition L 1} {Γ₁ Θ : Sequent L} {f : ℕ → O},
        (∀¹ χ).complexity ≤ r →
        (∀ n, f n < α) →
        (∀ n, OmegaDerivable A I r (f n) (I.inst χ n :: Γ₁)) →
        Γ₁ ⊆ (∀¹ χ) :: Θ →
        Δ₀ ⊆ ∼(∀¹ χ) :: Θ →
          OmegaDerivable A I r (OrdinalNotation.redOrd α δ) Θ := by
  intro δ Δ₀ he
  induction he with
  | @atom δ' φ hφT =>
      intro _ χ Γ₁ Θ f _ _ _ _ hssR
      have h := hssR List.mem_cons_self
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact absurd h (Literals.ne_exs (ψ := ∼χ) hφT)
      · refine OmegaDerivable.contraction ?_ (OmegaDerivable.atom hφT)
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rw [hx]; exact h
  | @identity δ' k rl v =>
      intro _ χ Γ₁ Θ f _ _ _ _ hssR
      refine of_mem_identity rl v ?_ ?_
      · have h := hssR (show Semiformula.rel rl v ∈
          [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      · have h := hssR (show Semiformula.nrel rl v ∈
          [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
  | @verum δ' =>
      intro _ χ Γ₁ Θ f _ _ _ _ hssR
      refine of_mem_verum ?_
      have h := hssR (show (⊤ : Proposition L) ∈ [(⊤ : Proposition L)] by simp)
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact absurd h (by simp)
      · exact h
  | @contraction δ' Δ' Δ ss _ ih =>
      intro hs χ Γ₁ Θ f hr hf hprem hssL hssR
      exact ih hs hr hf hprem hssL (fun x hx => hssR (ss hx))
  | @or δ' δ₀ ψ₁ ψ₂ Δ₁ hlt heP _ =>
      intro hs χ Γ₁ Θ f hr hf hprem hssL hssR
      have hd : OmegaDerivable A I r α ((∀¹ χ) :: Γ₁) :=
        OmegaDerivable.omegaRule f hf hprem
      have hmem : (ψ₁ ⋎ ψ₂) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
        hd hr (Θ := ψ₁ :: ψ₂ :: Θ)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssL hx
            simp only [List.mem_cons] at this
            tauto)
        heP
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · rcases hx with rfl | hx
            · tauto
            · have := hssR (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto)
      exact drop_head (OmegaDerivable.or (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @and δ' δ₀ δ₁ ψ₁ ψ₂ Δ₁ hlt₀ hlt₁ heP heQ _ _ =>
      intro hs χ Γ₁ Θ f hr hf hprem hssL hssR
      have hd : OmegaDerivable A I r α ((∀¹ χ) :: Γ₁) :=
        OmegaDerivable.omegaRule f hf hprem
      have hmem : (ψ₁ ⋏ ψ₂) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have hsubL : ∀ ζ : Proposition L, ((∀¹ χ) :: Γ₁) ⊆ (∀¹ χ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssL hx
          simp only [List.mem_cons] at this
          tauto
      have hsubR : ∀ ζ : Proposition L, ζ :: Δ₁ ⊆ ∼(∀¹ χ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssR (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto
      have kp := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs)
        hd hr (Θ := ψ₁ :: Θ) (hsubL ψ₁) heP (hsubR ψ₁)
      have kq := ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs)
        hd hr (Θ := ψ₂ :: Θ) (hsubL ψ₂) heQ (hsubR ψ₂)
      exact drop_head
        (OmegaDerivable.and (OrdinalNotation.redOrd_lt_right α hlt₀)
          (OrdinalNotation.redOrd_lt_right α hlt₁) kp kq) hmem
  | @omegaRule δ' ψ Δ₁ g hg heP _ =>
      intro hs χ Γ₁ Θ f hr hf hprem hssL hssR
      have hd : OmegaDerivable A I r α ((∀¹ χ) :: Γ₁) :=
        OmegaDerivable.omegaRule f hf hprem
      have hmem : (∀¹ ψ) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      refine drop_head
        (OmegaDerivable.omegaRule (fun n => OrdinalNotation.redOrd α (g n))
          (fun n => OrdinalNotation.redOrd_lt_right α (hg n)) (fun n => ?_)) hmem
      exact ih2 α (g n) (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α (hg n)) hs)
        hd hr (Θ := I.inst ψ n :: Θ)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssL hx
            simp only [List.mem_cons] at this
            tauto)
        (heP n)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto)
  | @exs δ' δ₀ ψ Δ₁ n hlt heP _ =>
      intro hs χ Γ₁ Θ f hr hf hprem hssL hssR
      have hd : OmegaDerivable A I r α ((∀¹ χ) :: Γ₁) :=
        OmegaDerivable.omegaRule f hf hprem
      by_cases hcase : (∃¹ ψ) = ∼(∀¹ χ)
      ·
        -- PRINCIPAL.  The witness is the existential side's `n`, and the ω-rule
        -- already has a premise at exactly that `n`.
        obtain rfl : ψ = ∼χ := by simpa using hcase
        have hcχ : ((I.inst χ n : Proposition L)).complexity < r := by
          simp only [Instantiation.complexity_inst] at *
          simp only [Semiformula.complexity_all] at hr
          omega
        have hA : OmegaDerivable A I r (OrdinalNotation.redOrd (f n) δ')
            ((I.inst χ n : Proposition L) :: Θ) :=
          ih2 (f n) δ' (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ' (hf n)) hs)
            (hprem n) hr
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hssL hx
                simp only [List.mem_cons] at this
                tauto)
            (OmegaDerivable.exs n hlt heP)
            (by
              intro x hx
              have := hssR hx
              simp only [List.mem_cons] at this ⊢
              tauto)
        have hBsub : OmegaDerivable A I r δ₀
            ((∼(I.inst χ n : Proposition L)) :: Δ₁) := by simpa using heP
        have hswap : OrdinalNotation.nadd δ₀ α < s := by
          rw [OrdinalNotation.nadd_comm]
          exact lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs
        have hrneg : (∼(∀¹ χ) : Proposition L).complexity ≤ r := by simpa using hr
        have hB : OmegaDerivable A I r (OrdinalNotation.redOrd δ₀ α)
            ((∼(I.inst χ n : Proposition L)) :: Θ) :=
          ih2 δ₀ α hswap hBsub hrneg
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hssR (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
            hd
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · left; simp
              · have := hssL hx
                simp only [List.mem_cons] at this
                rcases this with rfl | hm
                · left; simp
                · tauto)
        have hBlt : OrdinalNotation.redOrd δ₀ α < OrdinalNotation.redOrd α δ' := by
          have hlt' : OrdinalNotation.nadd δ₀ α < OrdinalNotation.nadd α δ' := by
            rw [OrdinalNotation.nadd_comm]
            exact OrdinalNotation.nadd_lt_nadd_right α hlt
          exact OrdinalNotation.sq_lt_sq hlt'
        refine OmegaDerivable.contraction ?_
          (OmegaDerivable.cut hcχ (OrdinalNotation.redOrd_lt_left δ' (hf n)) hBlt hA hB)
        intro x hx
        simp only [List.mem_append] at hx
        tauto
      · have hmem : (∃¹ ψ) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
          hd hr (Θ := I.inst ψ n :: Θ)
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hssL hx
              simp only [List.mem_cons] at this
              tauto)
          heP
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hssR (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto)
        exact drop_head (OmegaDerivable.exs n (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @cut δ' δ₀ δ₁ ψ Δ₁ Δ₂ hc hlt₀ hlt₁ hpp hnn _ _ =>
      intro hs χ Γ₁ Θ f hr hf hprem hssL hssR
      have hd : OmegaDerivable A I r α ((∀¹ χ) :: Γ₁) :=
        OmegaDerivable.omegaRule f hf hprem
      have hsubL : ∀ ζ : Proposition L, ((∀¹ χ) :: Γ₁) ⊆ (∀¹ χ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssL hx
          simp only [List.mem_cons] at this
          tauto
      have kp := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs)
        hd hr (Θ := ψ :: Θ) (hsubL ψ) hpp
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_left _ hx)
            simp only [List.mem_cons] at this
            tauto)
      have kn := ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs)
        hd hr (Θ := ∼ψ :: Θ) (hsubL (∼ψ)) hnn
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_right _ hx)
            simp only [List.mem_cons] at this
            tauto)
      refine OmegaDerivable.contraction ?_
        (OmegaDerivable.cut hc (OrdinalNotation.redOrd_lt_right α hlt₀)
          (OrdinalNotation.redOrd_lt_right α hlt₁) kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto

set_option maxHeartbeats 2000000 in
/-- Principal case for `∃`.  Mirror image of the ω-rule case: the numeral is the
existential side's own, and the ω-rule on the right has a premise at exactly
that numeral. -/
private theorem reduction_exs {r : ℕ} {s α α₀ : O}
    (ih2 : RedIHΩ L A I r s) (hα₀ : α₀ < α) :
    ∀ {δ : O} {Δ₀ : Sequent L}, OmegaDerivable A I r δ Δ₀ →
      OrdinalNotation.nadd α δ ≤ s →
      ∀ {χ : Semiproposition L 1} {n₀ : ℕ} {Γ₁ Θ : Sequent L},
        (∃¹ χ).complexity ≤ r →
        OmegaDerivable A I r α₀ (I.inst χ n₀ :: Γ₁) →
        Γ₁ ⊆ (∃¹ χ) :: Θ →
        Δ₀ ⊆ ∼(∃¹ χ) :: Θ →
          OmegaDerivable A I r (OrdinalNotation.redOrd α δ) Θ := by
  intro δ Δ₀ he
  induction he with
  | @atom δ' φ hφT =>
      intro _ χ n₀ Γ₁ Θ _ _ _ hssR
      have h := hssR List.mem_cons_self
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact absurd h (Literals.ne_all (ψ := ∼χ) hφT)
      · refine OmegaDerivable.contraction ?_ (OmegaDerivable.atom hφT)
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rw [hx]; exact h
  | @identity δ' k rl v =>
      intro _ χ n₀ Γ₁ Θ _ _ _ hssR
      refine of_mem_identity rl v ?_ ?_
      · have h := hssR (show Semiformula.rel rl v ∈
          [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      · have h := hssR (show Semiformula.nrel rl v ∈
          [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
  | @verum δ' =>
      intro _ χ n₀ Γ₁ Θ _ _ _ hssR
      refine of_mem_verum ?_
      have h := hssR (show (⊤ : Proposition L) ∈ [(⊤ : Proposition L)] by simp)
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact absurd h (by simp)
      · exact h
  | @contraction δ' Δ' Δ ss _ ih =>
      intro hs χ n₀ Γ₁ Θ hr hprem hssL hssR
      exact ih hs hr hprem hssL (fun x hx => hssR (ss hx))
  | @or δ' δ₀ ψ₁ ψ₂ Δ₁ hlt heP _ =>
      intro hs χ n₀ Γ₁ Θ hr hprem hssL hssR
      have hd : OmegaDerivable A I r α ((∃¹ χ) :: Γ₁) :=
        OmegaDerivable.exs n₀ hα₀ hprem
      have hmem : (ψ₁ ⋎ ψ₂) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
        hd hr (Θ := ψ₁ :: ψ₂ :: Θ)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssL hx
            simp only [List.mem_cons] at this
            tauto)
        heP
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · rcases hx with rfl | hx
            · tauto
            · have := hssR (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto)
      exact drop_head (OmegaDerivable.or (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @and δ' δ₀ δ₁ ψ₁ ψ₂ Δ₁ hlt₀ hlt₁ heP heQ _ _ =>
      intro hs χ n₀ Γ₁ Θ hr hprem hssL hssR
      have hd : OmegaDerivable A I r α ((∃¹ χ) :: Γ₁) :=
        OmegaDerivable.exs n₀ hα₀ hprem
      have hmem : (ψ₁ ⋏ ψ₂) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have hsubL : ∀ ζ : Proposition L, ((∃¹ χ) :: Γ₁) ⊆ (∃¹ χ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssL hx
          simp only [List.mem_cons] at this
          tauto
      have hsubR : ∀ ζ : Proposition L, ζ :: Δ₁ ⊆ ∼(∃¹ χ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssR (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto
      have kp := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs)
        hd hr (Θ := ψ₁ :: Θ) (hsubL ψ₁) heP (hsubR ψ₁)
      have kq := ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs)
        hd hr (Θ := ψ₂ :: Θ) (hsubL ψ₂) heQ (hsubR ψ₂)
      exact drop_head
        (OmegaDerivable.and (OrdinalNotation.redOrd_lt_right α hlt₀)
          (OrdinalNotation.redOrd_lt_right α hlt₁) kp kq) hmem
  | @omegaRule δ' ψ Δ₁ g hg heP _ =>
      intro hs χ n₀ Γ₁ Θ hr hprem hssL hssR
      have hd : OmegaDerivable A I r α ((∃¹ χ) :: Γ₁) :=
        OmegaDerivable.exs n₀ hα₀ hprem
      by_cases hcase : (∀¹ ψ) = ∼(∃¹ χ)
      ·
        -- PRINCIPAL.  The ω-rule on the right has a premise at every numeral,
        -- so in particular at the one the existential side chose.
        obtain rfl : ψ = ∼χ := by simpa using hcase
        have hcχ : ((I.inst χ n₀ : Proposition L)).complexity < r := by
          simp only [Instantiation.complexity_inst] at *
          simp only [Semiformula.complexity_exs] at hr
          omega
        have hA : OmegaDerivable A I r (OrdinalNotation.redOrd α₀ δ')
            ((I.inst χ n₀ : Proposition L) :: Θ) :=
          ih2 α₀ δ' (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ' hα₀) hs) hprem hr
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hssL hx
                simp only [List.mem_cons] at this
                tauto)
            (OmegaDerivable.omegaRule g hg heP)
            (by
              intro x hx
              have := hssR hx
              simp only [List.mem_cons] at this ⊢
              tauto)
        have hBsub : OmegaDerivable A I r (g n₀)
            ((∼(I.inst χ n₀ : Proposition L)) :: Δ₁) := by simpa using heP n₀
        have hswap : OrdinalNotation.nadd (g n₀) α < s := by
          rw [OrdinalNotation.nadd_comm]
          exact lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α (hg n₀)) hs
        have hrneg : (∼(∃¹ χ) : Proposition L).complexity ≤ r := by simpa using hr
        have hB : OmegaDerivable A I r (OrdinalNotation.redOrd (g n₀) α)
            ((∼(I.inst χ n₀ : Proposition L)) :: Θ) :=
          ih2 (g n₀) α hswap hBsub hrneg
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hssR (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
            hd
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · left; simp
              · have := hssL hx
                simp only [List.mem_cons] at this
                rcases this with rfl | hm
                · left; simp
                · tauto)
        have hBlt : OrdinalNotation.redOrd (g n₀) α < OrdinalNotation.redOrd α δ' := by
          have hlt' : OrdinalNotation.nadd (g n₀) α < OrdinalNotation.nadd α δ' := by
            rw [OrdinalNotation.nadd_comm]
            exact OrdinalNotation.nadd_lt_nadd_right α (hg n₀)
          exact OrdinalNotation.sq_lt_sq hlt'
        refine OmegaDerivable.contraction ?_
          (OmegaDerivable.cut hcχ (OrdinalNotation.redOrd_lt_left δ' hα₀) hBlt hA hB)
        intro x hx
        simp only [List.mem_append] at hx
        tauto
      · have hmem : (∀¹ ψ) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        refine drop_head
          (OmegaDerivable.omegaRule (fun n => OrdinalNotation.redOrd α (g n))
            (fun n => OrdinalNotation.redOrd_lt_right α (hg n)) (fun n => ?_)) hmem
        exact ih2 α (g n) (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α (hg n)) hs)
          hd hr (Θ := I.inst ψ n :: Θ)
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hssL hx
              simp only [List.mem_cons] at this
              tauto)
          (heP n)
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hssR (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto)
  | @exs δ' δ₀ ψ Δ₁ n hlt heP _ =>
      intro hs χ n₀ Γ₁ Θ hr hprem hssL hssR
      have hd : OmegaDerivable A I r α ((∃¹ χ) :: Γ₁) :=
        OmegaDerivable.exs n₀ hα₀ hprem
      have hmem : (∃¹ ψ) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
        hd hr (Θ := I.inst ψ n :: Θ)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssL hx
            simp only [List.mem_cons] at this
            tauto)
        heP
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto)
      exact drop_head (OmegaDerivable.exs n (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @cut δ' δ₀ δ₁ ψ Δ₁ Δ₂ hc hlt₀ hlt₁ hpp hnn _ _ =>
      intro hs χ n₀ Γ₁ Θ hr hprem hssL hssR
      have hd : OmegaDerivable A I r α ((∃¹ χ) :: Γ₁) :=
        OmegaDerivable.exs n₀ hα₀ hprem
      have hsubL : ∀ ζ : Proposition L, ((∃¹ χ) :: Γ₁) ⊆ (∃¹ χ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssL hx
          simp only [List.mem_cons] at this
          tauto
      have kp := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs)
        hd hr (Θ := ψ :: Θ) (hsubL ψ) hpp
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_left _ hx)
            simp only [List.mem_cons] at this
            tauto)
      have kn := ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs)
        hd hr (Θ := ∼ψ :: Θ) (hsubL (∼ψ)) hnn
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_right _ hx)
            simp only [List.mem_cons] at this
            tauto)
      refine OmegaDerivable.contraction ?_
        (OmegaDerivable.cut hc (OrdinalNotation.redOrd_lt_right α hlt₀)
          (OrdinalNotation.redOrd_lt_right α hlt₁) kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto

set_option maxHeartbeats 2000000 in
/-- Principal case for an atomic axiom: the left derivation *is* an axiom `ψ`.

The right derivation must produce `∼ψ`.  Only three rules can put a literal at
the head of a sequent: the identity rule, which then carries `ψ` itself in the
same sequent, so weakening the axiom suffices; the axiom rule, which is ruled
out by consistency; and `verum`, ruled out because `∼ψ` is a literal.  Every
other rule is non-principal and recurses. -/
private theorem reduction_atom {r : ℕ} {s α : O}
    (ih2 : RedIHΩ L A I r s) :
    ∀ {δ : O} {Δ₀ : Sequent L}, OmegaDerivable A I r δ Δ₀ →
      OrdinalNotation.nadd α δ ≤ s →
      ∀ {ψ : Proposition L} {Θ : Sequent L},
        A.T ψ → Δ₀ ⊆ ∼ψ :: Θ →
          OmegaDerivable A I r (OrdinalNotation.redOrd α δ) Θ := by
  intro δ Δ₀ he
  induction he with
  | @atom δ' φ hφ =>
      intro _ ψ Θ hψ hssR
      have h := hssR List.mem_cons_self
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact absurd hφ (A.consistent ψ hψ)
      · refine OmegaDerivable.contraction ?_ (OmegaDerivable.atom hφ)
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rw [hx]; exact h
  | @identity δ' k rl v =>
      intro _ ψ Θ hψ hssR
      have hp := hssR (show Semiformula.rel rl v ∈
        [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
      have hn := hssR (show Semiformula.nrel rl v ∈
        [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hn
      rcases hp with hpψ | hpΘ
      · rcases hn with hnψ | hnΘ
        · exact absurd (hpψ.trans hnψ.symm) (by simp)
        · have e : ψ = Semiformula.nrel rl v := by
            rw [← Semiformula.neg_rel, hpψ]; simp
          refine OmegaDerivable.contraction ?_ (OmegaDerivable.atom hψ)
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rw [hx, e]; exact hnΘ
      · rcases hn with hnψ | hnΘ
        · have e : ψ = Semiformula.rel rl v := by
            rw [← Semiformula.neg_nrel, hnψ]; simp
          refine OmegaDerivable.contraction ?_ (OmegaDerivable.atom hψ)
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rw [hx, e]; exact hpΘ
        · exact of_mem_identity rl v hpΘ hnΘ
  | @verum δ' =>
      intro _ ψ Θ hψ hssR
      have h := hssR (show (⊤ : Proposition L) ∈ [(⊤ : Proposition L)] by simp)
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact absurd h.symm (Literals.neg_ne_verum hψ)
      · exact of_mem_verum h
  | @contraction δ' Δ' Δ ss _ ih =>
      intro hs ψ Θ hψ hssR
      exact ih hs hψ (fun x hx => hssR (ss hx))
  | @or δ' δ₀ ψ₁ ψ₂ Δ₁ hlt heP _ =>
      intro hs ψ Θ hψ hssR
      have hr : ψ.complexity ≤ r := by
        obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal ψ hψ <;> simp
      have hmem : (ψ₁ ⋎ ψ₂) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm (Literals.neg_ne_or hψ)
        · exact h
      have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
        (OmegaDerivable.atom hψ) hr (Θ := ψ₁ :: ψ₂ :: Θ)
        (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
          tauto)
        heP
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · rcases hx with rfl | hx
            · tauto
            · have := hssR (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto)
      exact drop_head (OmegaDerivable.or (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @and δ' δ₀ δ₁ ψ₁ ψ₂ Δ₁ hlt₀ hlt₁ heP heQ _ _ =>
      intro hs ψ Θ hψ hssR
      have hr : ψ.complexity ≤ r := by
        obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal ψ hψ <;> simp
      have hmem : (ψ₁ ⋏ ψ₂) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm (Literals.neg_ne_and hψ)
        · exact h
      have hsubL : ∀ ζ : Proposition L, ([ψ] : Sequent L) ⊆ ψ :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        tauto
      have hsubR : ∀ ζ : Proposition L, ζ :: Δ₁ ⊆ ∼ψ :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssR (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto
      have kp := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs)
        (OmegaDerivable.atom hψ) hr (Θ := ψ₁ :: Θ) (hsubL ψ₁) heP (hsubR ψ₁)
      have kq := ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs)
        (OmegaDerivable.atom hψ) hr (Θ := ψ₂ :: Θ) (hsubL ψ₂) heQ (hsubR ψ₂)
      exact drop_head
        (OmegaDerivable.and (OrdinalNotation.redOrd_lt_right α hlt₀)
          (OrdinalNotation.redOrd_lt_right α hlt₁) kp kq) hmem
  | @omegaRule δ' χ Δ₁ f hf heP _ =>
      intro hs ψ Θ hψ hssR
      have hr : ψ.complexity ≤ r := by
        obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal ψ hψ <;> simp
      have hmem : (∀¹ χ) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm (Literals.neg_ne_all hψ)
        · exact h
      refine drop_head
        (OmegaDerivable.omegaRule (fun n => OrdinalNotation.redOrd α (f n))
          (fun n => OrdinalNotation.redOrd_lt_right α (hf n)) (fun n => ?_)) hmem
      exact ih2 α (f n) (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α (hf n)) hs)
        (OmegaDerivable.atom hψ) hr (Θ := I.inst χ n :: Θ)
        (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
          tauto)
        (heP n)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto)
  | @exs δ' δ₀ χ Δ₁ n hlt heP _ =>
      intro hs ψ Θ hψ hssR
      have hr : ψ.complexity ≤ r := by
        obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal ψ hψ <;> simp
      have hmem : (∃¹ χ) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm (Literals.neg_ne_exs hψ)
        · exact h
      have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
        (OmegaDerivable.atom hψ) hr (Θ := I.inst χ n :: Θ)
        (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
          tauto)
        heP
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto)
      exact drop_head (OmegaDerivable.exs n (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @cut δ' δ₀ δ₁ χ Δ₁ Δ₂ hc hlt₀ hlt₁ hpp hnn _ _ =>
      intro hs ψ Θ hψ hssR
      have hr : ψ.complexity ≤ r := by
        obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal ψ hψ <;> simp
      have hsubL : ∀ ζ : Proposition L, ([ψ] : Sequent L) ⊆ ψ :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        tauto
      have kp := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs)
        (OmegaDerivable.atom hψ) hr (Θ := χ :: Θ) (hsubL χ) hpp
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_left _ hx)
            simp only [List.mem_cons] at this
            tauto)
      have kn := ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs)
        (OmegaDerivable.atom hψ) hr (Θ := ∼χ :: Θ) (hsubL (∼χ)) hnn
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_right _ hx)
            simp only [List.mem_cons] at this
            tauto)
      refine OmegaDerivable.contraction ?_
        (OmegaDerivable.cut hc (OrdinalNotation.redOrd_lt_right α hlt₀)
          (OrdinalNotation.redOrd_lt_right α hlt₁) kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto

/-! ### The reduction lemma itself -/

set_option maxHeartbeats 2000000 in
/-- The reduction lemma in the form the well-founded recursion needs. -/
private theorem reduction_aux {r : ℕ} :
    ∀ (s β γ : O), OrdinalNotation.nadd β γ ≤ s →
      ∀ {Γ₀ : Sequent L}, OmegaDerivable A I r β Γ₀ →
        ∀ {φ : Proposition L}, φ.complexity ≤ r →
        ∀ {Θ Δ₀ : Sequent L}, Γ₀ ⊆ φ :: Θ →
          OmegaDerivable A I r γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ →
            OmegaDerivable A I r (OrdinalNotation.redOrd β γ) Θ := by
  intro s
  induction s using WellFoundedLT.induction with
  | _ s ihs =>
    intro β γ hbg
    have ih2 : RedIHΩ L A I r (OrdinalNotation.nadd β γ) := fun β' γ' h =>
      ihs (OrdinalNotation.nadd β' γ') (lt_of_lt_of_le h hbg) β' γ' le_rfl
    suffices K : ∀ (α : O) {Γ₀ : Sequent L}, OmegaDerivable A I r α Γ₀ →
        OrdinalNotation.nadd α γ ≤ OrdinalNotation.nadd β γ →
        ∀ {φ : Proposition L}, φ.complexity ≤ r →
        ∀ {Θ Δ₀ : Sequent L}, Γ₀ ⊆ φ :: Θ →
          OmegaDerivable A I r γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ →
            OmegaDerivable A I r (OrdinalNotation.redOrd α γ) Θ by
      intro Γ₀ hd φ hφ Θ Δ₀ hss he hst
      exact K β hd le_rfl hφ hss he hst
    intro α Γ₀ hd
    induction hd with
    | @atom α' ψ hψ =>
        intro hs φ _ Θ Δ₀ hss he hst
        have h := hss List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with rfl | hΘ
        · exact reduction_atom ih2 he hs hψ hst
        · refine OmegaDerivable.contraction ?_ (OmegaDerivable.atom hψ)
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rw [hx]; exact hΘ
    | @contraction α' Δ' Γ' ss _ ihprem =>
        intro hs φ hφ Θ Δ₀ hss he hst
        exact ihprem hs hφ (fun x hx => hss (ss hx)) he hst
    | @identity α' k rl v =>
        intro _ φ _ Θ Δ₀ hss he hst
        have hle : γ ≤ OrdinalNotation.redOrd α' γ :=
          le_trans (OrdinalNotation.le_nadd_right α' γ) (OrdinalNotation.le_nadd_left _ _)
        have hp := hss (show Semiformula.rel rl v ∈
          [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
        have hn := hss (show Semiformula.nrel rl v ∈
          [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hn
        rcases hp with hpφ | hpΘ
        · have hnΘ : (∼φ : Proposition L) ∈ Θ := by
            rcases hn with hnφ | hnΘ
            · exact absurd (hpφ.trans hnφ.symm) (by simp)
            · rw [← hpφ]; simpa using hnΘ
          exact (OmegaDerivable.contraction
            (fun x hx => by
              have := hst hx
              simp only [List.mem_cons] at this
              rcases this with rfl | hm
              · exact hnΘ
              · exact hm) he).mono_ord hle
        · rcases hn with hnφ | hnΘ
          · have hpΘ' : (∼φ : Proposition L) ∈ Θ := by
              rw [← hnφ]; simpa using hpΘ
            exact (OmegaDerivable.contraction
              (fun x hx => by
                have := hst hx
                simp only [List.mem_cons] at this
                rcases this with rfl | hm
                · exact hpΘ'
                · exact hm) he).mono_ord hle
          · exact of_mem_identity rl v hpΘ hnΘ
    | @verum α' =>
        intro _ φ _ Θ Δ₀ hss he hst
        have h := hss (show (⊤ : Proposition L) ∈ [(⊤ : Proposition L)] by simp)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with hφ | hΘ
        · have hbot : Δ₀ ⊆ (⊥ : Proposition L) :: Θ := by
            intro x hx
            have := hst hx
            simp only [List.mem_cons] at this ⊢
            rcases this with rfl | hm
            · left; rw [← hφ]; simp
            · tauto
          exact (drop_falsum he hbot).mono_ord
            (le_trans (OrdinalNotation.le_nadd_right α' γ) (OrdinalNotation.le_nadd_left _ _))
        · exact of_mem_verum hΘ
    | @or α' α₀ χ ρ Γ' hb hprem ihp =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (χ ⋎ ρ) = φ
        · subst hcase
          exact reduction_or ih2 hb he hs hφ hprem
            (fun x hx => hss (List.mem_cons_of_mem _ hx)) hst
        · have hmem : (χ ⋎ ρ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          have hs' : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb) hs)
          have key := ihp hs' hφ (Θ := χ :: ρ :: Θ)
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · rcases hx with rfl | hx
                · tauto
                · have := hss (List.mem_cons_of_mem _ hx)
                  simp only [List.mem_cons] at this
                  tauto)
            he
            (by
              intro x hx
              have := hst hx
              simp only [List.mem_cons] at this ⊢
              tauto)
          exact drop_head (OmegaDerivable.or (OrdinalNotation.redOrd_lt_left γ hb) key) hmem
    | @and α' α₀ α₁ χ ρ Γ' hb1 hb2 hp hq ihp ihq =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (χ ⋏ ρ) = φ
        · subst hcase
          exact reduction_and ih2 hb1 hb2 he hs hφ hp hq
            (fun x hx => hss (List.mem_cons_of_mem _ hx)) hst
        · have hmem : (χ ⋏ ρ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          have hs1 : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb1) hs)
          have hs2 : OrdinalNotation.nadd α₁ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb2) hs)
          have hsubL : ∀ ζ : Proposition L, (ζ :: Γ') ⊆ φ :: ζ :: Θ := by
            intro ζ x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hss (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto
          have hsubR : ∀ ζ : Proposition L, Δ₀ ⊆ ∼φ :: ζ :: Θ := by
            intro ζ x hx
            have := hst hx
            simp only [List.mem_cons] at this ⊢
            tauto
          have kp := ihp hs1 hφ (Θ := χ :: Θ) (hsubL χ) he (hsubR χ)
          have kq := ihq hs2 hφ (Θ := ρ :: Θ) (hsubL ρ) he (hsubR ρ)
          exact drop_head
            (OmegaDerivable.and (OrdinalNotation.redOrd_lt_left γ hb1)
              (OrdinalNotation.redOrd_lt_left γ hb2) kp kq) hmem
    | @omegaRule α' χ Γ' f hf hprem ihp =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (∀¹ χ) = φ
        · subst hcase
          exact reduction_omega ih2 he hs hφ hf hprem
            (fun x hx => hss (List.mem_cons_of_mem _ hx)) hst
        · have hmem : (∀¹ χ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          -- no shift: the ω-rule keeps its context, so the recursion is direct
          refine drop_head
            (OmegaDerivable.omegaRule (fun n => OrdinalNotation.redOrd (f n) γ)
              (fun n => OrdinalNotation.redOrd_lt_left γ (hf n)) (fun n => ?_)) hmem
          refine ihp n (le_of_lt (lt_of_lt_of_le
            (OrdinalNotation.nadd_lt_nadd_left γ (hf n)) hs)) hφ (Θ := I.inst χ n :: Θ) ?_ he ?_
          · intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hss (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto
          · intro x hx
            have := hst hx
            simp only [List.mem_cons] at this ⊢
            tauto
    | @exs α' α₀ χ Γ' n hb hprem ihp =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (∃¹ χ) = φ
        · subst hcase
          exact reduction_exs ih2 hb he hs hφ hprem
            (fun x hx => hss (List.mem_cons_of_mem _ hx)) hst
        · have hmem : (∃¹ χ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          have hs' : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb) hs)
          have key := ihp hs' hφ (Θ := I.inst χ n :: Θ)
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hss (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
            he
            (by
              intro x hx
              have := hst hx
              simp only [List.mem_cons] at this ⊢
              tauto)
          exact drop_head
            (OmegaDerivable.exs n (OrdinalNotation.redOrd_lt_left γ hb) key) hmem
    | @cut α' α₀ α₁ χ Γ₁ Γ₂ hc hb1 hb2 hpp hnn ihp ihn =>
        intro hs φ hφ Θ Δ₀ hss he hst
        have hs1 : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
          le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb1) hs)
        have hs2 : OrdinalNotation.nadd α₁ γ ≤ OrdinalNotation.nadd β γ :=
          le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb2) hs)
        have hsubR : ∀ ζ : Proposition L, Δ₀ ⊆ ∼φ :: ζ :: Θ := by
          intro ζ x hx
          have := hst hx
          simp only [List.mem_cons] at this ⊢
          tauto
        have kp := ihp hs1 hφ (Θ := χ :: Θ)
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hss (List.mem_append_left _ hx)
              simp only [List.mem_cons] at this
              tauto)
          he (hsubR χ)
        have kn := ihn hs2 hφ (Θ := ∼χ :: Θ)
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hss (List.mem_append_right _ hx)
              simp only [List.mem_cons] at this
              tauto)
          he (hsubR (∼χ))
        refine OmegaDerivable.contraction ?_
          (OmegaDerivable.cut hc (OrdinalNotation.redOrd_lt_left γ hb1)
            (OrdinalNotation.redOrd_lt_left γ hb2) kp kn)
        intro x hx
        simp only [List.mem_append] at hx
        tauto

/-- **Reduction, infinitary.**  Two derivations that cut against each other on a
formula of complexity at most `r` combine into one that uses only cuts of
complexity below `r`. -/
theorem reduction {r : ℕ} (β γ : O) {Γ₀ Δ₀ Θ : Sequent L} {φ : Proposition L}
    (hφ : φ.complexity ≤ r)
    (hd : OmegaDerivable A I r β Γ₀) (hss : Γ₀ ⊆ φ :: Θ)
    (he : OmegaDerivable A I r γ Δ₀) (hst : Δ₀ ⊆ ∼φ :: Θ) :
    OmegaDerivable A I r (OrdinalNotation.redOrd β γ) Θ :=
  reduction_aux (OrdinalNotation.nadd β γ) β γ le_rfl hd hφ hss he hst

/-! ### Elimination and cut elimination -/

/-- One level of cut rank, at the cost of one `ω`-power. -/
theorem elimination {r : ℕ} :
    ∀ {α : O} {Γ : Sequent L}, OmegaDerivable A I (r + 1) α Γ →
      OmegaDerivable A I r (OrdinalNotation.omegaPow α) Γ := by
  intro α Γ h
  induction h with
  | atom h => exact .atom h
  | identity rl v => exact .identity rl v
  | verum => exact .verum
  | or hlt _ ih => exact .or (OrdinalNotation.omegaPow_lt_omegaPow hlt) ih
  | and hb hc _ _ ihp ihq =>
      exact .and (OrdinalNotation.omegaPow_lt_omegaPow hb)
        (OrdinalNotation.omegaPow_lt_omegaPow hc) ihp ihq
  | omegaRule f hf _ ih =>
      exact .omegaRule (fun n => OrdinalNotation.omegaPow (f n))
        (fun n => OrdinalNotation.omegaPow_lt_omegaPow (hf n)) ih
  | exs n hlt _ ih => exact .exs n (OrdinalNotation.omegaPow_lt_omegaPow hlt) ih
  | contraction ss _ ih => exact .contraction ss ih
  | @cut α' β' γ' φ Γ₁ Γ₂ hcomp hb hc _ _ ihp ihn =>
      have hφ : φ.complexity ≤ r := Nat.lt_succ_iff.mp hcomp
      have hkey := reduction (OrdinalNotation.omegaPow β') (OrdinalNotation.omegaPow γ')
        (Θ := Γ₁ ++ Γ₂) hφ ihp
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr (List.mem_append_left _ hx))
        ihn
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr (List.mem_append_right _ hx))
      exact hkey.mono_ord
        (le_of_lt (OrdinalNotation.redOrd_lt_omegaPow
          (OrdinalNotation.omegaPow_lt_omegaPow hb) (OrdinalNotation.omegaPow_lt_omegaPow hc)))

/-- **Cut elimination, infinitary.**  Rank `r` at height `α` becomes cut free at
height the `r`-fold `ω`-tower over `α`.  Taking the notation system to be
`NONote` puts the bound below `ε₀`, because that is the type of notations
below `ε₀`; a larger notation system gives a larger bound and nothing else in
this file changes. -/
theorem cutElimination :
    ∀ (r : ℕ) {α : O} {Γ : Sequent L}, OmegaDerivable A I r α Γ →
      OmegaDerivable A I 0 (OrdinalNotation.omegaTower r α) Γ := by
  intro r
  induction r with
  | zero => intro α Γ h; exact h
  | succ r ih => intro α Γ h; exact ih (elimination h)

end OmegaDerivable

end OrdinalAnalysis
