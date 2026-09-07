/-
  The reduction lemma — the gatekeeper of Gentzen's argument.

  Given two derivations that cut against each other on a formula of complexity
  at most `r`, it produces a derivation of the combined sequent that uses only
  cuts of complexity strictly below `r`.  It is what lets the elimination lemma
  peel the cut rank down one level at a time, and it is the only place the
  natural sum is unavoidable.

  Four things fix the shape of the proof, and each of them was arrived at by
  first trying the obvious alternative.

  * Both sequents are related to the target by `⊆` rather than being literally
    `φ :: Θ`.  Foundation's structural rule is subset-based, so from a
    head-shaped hypothesis the `contraction` case learns nothing about the shape
    of its premise and the induction cannot proceed.

  * There is no inversion lemma anywhere in this file, and there cannot be one.
    The natural plan — induct on the left derivation, and in the principal case
    invert the right one to expose the subformulas of `∼φ` — breaks at the
    universal quantifier, where it would need an inversion for `∃`.  No such
    lemma exists: the witness a derivation chose is not recoverable from its
    conclusion.  Both quantifier cases instead take the witness from whichever
    premise has one and instantiate the other side at it.

  * The recursion is on the *symmetric* measure `β ⊕ γ`.  The quantifier
    principal cases produce their second cut premise by running the reduction
    with the two sides swapped, and a measure counting only the left ordinal
    cannot see that as a decrease.

  * The ordinal delivered is `(β ⊕ γ) ⊕ (β ⊕ γ)`, not the textbook `β ⊕ γ`.
    The propositional principal cases perform two *nested* cuts, so they need
    two strictly increasing ordinals above everything the hypotheses return, and
    the plain natural sum supplies only one.  Doubling is the cheapest repair
    that survives the recursion, and the elimination lemma will absorb it,
    because `ω ^ α` is additively indecomposable.
-/
import OrdinalAnalysis.Ordinal.NaturalSumMono
import OrdinalAnalysis.Proof.Inversion
import OrdinalAnalysis.Proof.InversionAll

namespace OrdinalAnalysis

open LO LO.FirstOrder LO.FirstOrder.Derivation
open ONote

variable {L : Language}

namespace BoundedDerivable

/-- A sequent that already contains both an atom and its negation is derivable
outright, so the cut against an atomic formula never needs the cut rule. -/
theorem of_mem_identity {r : ℕ} {α : NONote} {Θ : Sequent L} {k : ℕ}
    (rl : L.Rel k) (v) (hp : Semiformula.rel rl v ∈ Θ)
    (hn : Semiformula.nrel rl v ∈ Θ) : BoundedDerivable r α Θ := by
  refine .contraction ?_ (.identity rl v)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hp
  · exact hn

/-- `⊤` in a sequent makes it derivable outright. -/
theorem of_mem_verum {r : ℕ} {α : NONote} {Θ : Sequent L}
    (h : (⊤ : Proposition L) ∈ Θ) : BoundedDerivable r α Θ := by
  refine .contraction ?_ .verum
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl
  exact h

/-- `⊥` is a passenger: no rule introduces it, so it can only have entered by
weakening and can be dropped again.

Informal presentations skip this; a formalisation cannot, because the cut
formula `⊤` has `∼⊤ = ⊥` and the reduction lemma then has to discharge a
sequent carrying a `⊥`. -/
theorem drop_falsum {r : ℕ} :
    ∀ {α : NONote} {Γ : Sequent L}, BoundedDerivable r α Γ →
      ∀ {Θ : Sequent L}, Γ ⊆ (⊥ : Proposition L) :: Θ →
        BoundedDerivable r α Θ := by
  intro α Γ h
  induction h with
  | identity rl v =>
      intro Θ hss
      refine of_mem_identity rl v ?_ ?_
      · have := hss (by simp : Semiformula.rel rl v ∈ [_, _])
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      · have := hss (by simp : Semiformula.nrel rl v ∈ [_, _])
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
  | verum =>
      intro Θ hss
      refine of_mem_verum ?_
      have := hss (by simp : (⊤ : Proposition L) ∈ [(⊤ : Proposition L)])
      simp only [List.mem_cons] at this
      rcases this with hbot | hm
      · exact absurd hbot (by simp)
      · exact hm
  | @or α β χ ρ Γ' hlt _ ih =>
      intro Θ hss
      have hmem : (χ ⋎ ρ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have key := ih (Θ := χ :: ρ :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | rfl | hx
        · tauto
        · tauto
        · have := hss (by simp only [List.mem_cons]; tauto)
          simp only [List.mem_cons] at this
          tauto)
      exact .contraction (by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hmem
        · exact hx) (BoundedDerivable.or hlt key)
  | @and α β γ χ ρ Γ' hβ hγ _ _ ihp ihq =>
      intro Θ hss
      have hmem : (χ ⋏ ρ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have kp := ihp (Θ := χ :: Θ) (by
        intro x hx; simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (by simp only [List.mem_cons]; tauto)
          simp only [List.mem_cons] at this; tauto)
      have kq := ihq (Θ := ρ :: Θ) (by
        intro x hx; simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (by simp only [List.mem_cons]; tauto)
          simp only [List.mem_cons] at this; tauto)
      exact .contraction (by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hmem
        · exact hx) (BoundedDerivable.and hβ hγ kp kq)
  | @all α β χ Γ' hlt _ ih =>
      intro Θ hss
      have hmem : (∀¹ χ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have key := ih (Θ := χ.free :: Θ⁺) (by
        intro x hx
        simp only [Rewriting.shifts_cons, List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · simp only [Rewriting.shifts, List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := hss (show y ∈ (∀¹ χ) :: Γ' by simp only [List.mem_cons]; tauto)
          simp only [List.mem_cons] at this
          rcases this with rfl | hm
          · left; simp
          · right; right
            simp only [Rewriting.shifts, List.mem_map]
            exact ⟨y, hm, rfl⟩)
      exact .contraction (by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hmem
        · exact hx) (BoundedDerivable.all hlt key)
  | @exs α β χ Γ' t hlt _ ih =>
      intro Θ hss
      have hmem : (∃¹ χ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have key := ih (Θ := χ/[t] :: Θ) (by
        intro x hx; simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (by simp only [List.mem_cons]; tauto)
          simp only [List.mem_cons] at this; tauto)
      exact .contraction (by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hmem
        · exact hx) (BoundedDerivable.exs t hlt key)
  | @contraction α Δ Γ' ss _ ih =>
      intro Θ hss
      exact ih (fun x hx => hss (ss hx))
  | @cut α β γ χ Γ₁ Γ₂ hc hβ hγ _ _ ihp ihn =>
      intro Θ hss
      have kp := ihp (Θ := χ :: Θ) (by
        intro x hx; simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_append_left _ hx)
          simp only [List.mem_cons] at this; tauto)
      have kn := ihn (Θ := ∼χ :: Θ) (by
        intro x hx; simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_append_right _ hx)
          simp only [List.mem_cons] at this; tauto)
      refine .contraction ?_ (BoundedDerivable.cut hc hβ hγ kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto

/-- If the head of a derivable sequent already occurs in its tail, drop it.

This one line covers every case of the reduction where no cut is performed:
the cut formula is an atom whose dual the other side already carries, or it is
`⊤`, or the sequent is closed for an unrelated reason. -/
theorem drop_head {r : ℕ} {α : NONote} {ψ : Proposition L} {Θ : Sequent L}
    (h : BoundedDerivable r α (ψ :: Θ)) (hmem : ψ ∈ Θ) : BoundedDerivable r α Θ := by
  refine .contraction ?_ h
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hmem
  · exact hx

/-! ### The reduction lemma

The recursion has two layers.  A well-founded recursion on `β ⊕ γ` handles
every case that consumes an ordinal; a structural induction on each derivation
handles `contraction`, which does not consume one. -/

set_option linter.unusedVariables false in
/-! ### The principal cases

Each of the four principal cases is a lemma of its own, because each runs a
*second* structural induction — on the right derivation — in order to find the
rule that introduced `∼φ`.  They take the outer induction hypothesis as an
argument; `RedIH` names its shape. -/

/-- The statement of `reduction` at a fixed left ordinal, packaged so that the
principal-case lemmas can take the outer induction hypothesis as an argument. -/
def RedIH (L : Language) (r : ℕ) (β : NONote) : Prop :=
  ∀ {Γ₀ : Sequent L}, BoundedDerivable r β Γ₀ →
    ∀ {φ : Proposition L}, φ.complexity ≤ r →
    ∀ {Θ Δ₀ : Sequent L} {γ : NONote}, Γ₀ ⊆ φ :: Θ →
      BoundedDerivable r γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ →
        BoundedDerivable r (NONote.redOrd β γ) Θ


/-- The same statement, but indexed by the *symmetric* measure `β ⊕ γ` rather
than by the left ordinal alone.

The quantifier principal cases force this.  Their second cut premise is obtained
by running the reduction with the two sides *swapped* — the right premise becomes
the left, and the whole left derivation becomes the right — and a measure that
counts only the left ordinal cannot see that as a decrease.  The natural sum
can, because it is commutative. -/
def RedIH2 (L : Language) (r : ℕ) (s : NONote) : Prop :=
  ∀ (β γ : NONote), NONote.nadd β γ < s →
    ∀ {Γ₀ : Sequent L}, BoundedDerivable r β Γ₀ →
      ∀ {φ : Proposition L}, φ.complexity ≤ r →
      ∀ {Θ Δ₀ : Sequent L}, Γ₀ ⊆ φ :: Θ →
        BoundedDerivable r γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ →
          BoundedDerivable r (NONote.redOrd β γ) Θ

set_option maxHeartbeats 2000000 in
/-- Principal case for `⋎`: the left derivation ended by introducing the cut
formula `χ ⋎ ρ`.

The induction is structural on the *right* derivation, which is what locates the
`⋏` that introduced `∼(χ ⋎ ρ)`.  Once found, all three inputs to the two cuts
come from `ih2`, at the pairs `(α₀, δ)`, `(α, δ₀)` and `(α, δ₁)`, each below
`(α, δ)` in the natural sum.  `NONote.mid` supplies the value the inner cut runs
at, which is the one thing the textbook bound `α ⊕ δ` cannot provide. -/
private theorem reduction_or {r : ℕ} {s α α₀ : NONote}
    (ih2 : RedIH2 L r s) (hα₀ : α₀ < α) :
    ∀ {δ : NONote} {Δ₀ : Sequent L}, BoundedDerivable r δ Δ₀ →
      NONote.nadd α δ ≤ s →
      ∀ {χ ρ : Proposition L} {Γ₁ Θ : Sequent L},
        (χ ⋎ ρ).complexity ≤ r →
        BoundedDerivable r α₀ (χ :: ρ :: Γ₁) →
        Γ₁ ⊆ (χ ⋎ ρ) :: Θ →
        Δ₀ ⊆ ∼(χ ⋎ ρ) :: Θ →
          BoundedDerivable r (NONote.redOrd α δ) Θ := by
  intro δ Δ₀ he
  induction he with
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
  | @or δ' δ₀ ψ₁ ψ₂ Δ₁ hlt _ ih =>
      intro hs χ ρ Γ₁ Θ hr hprem hssL hssR
      have hs' : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs)
      have hmem : (ψ₁ ⋎ ψ₂) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih hs' (χ := χ) (ρ := ρ) (Γ₁ := Γ₁) (Θ := ψ₁ :: ψ₂ :: Θ) hr hprem
        (by
          intro x hx
          have := hssL hx
          simp only [List.mem_cons] at this ⊢
          tauto)
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
      exact drop_head (BoundedDerivable.or (NONote.redOrd_lt_right α hlt) key) hmem
  | @and δ' δ₀ δ₁ ψ₁ ψ₂ Δ₁ hlt₀ hlt₁ heP heQ ihP ihQ =>
      intro hs χ ρ Γ₁ Θ hr hprem hssL hssR
      have hs₀ : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₀) hs)
      have hs₁ : NONote.nadd α δ₁ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₁) hs)
      by_cases hcase : (ψ₁ ⋏ ψ₂) = ∼(χ ⋎ ρ)
      ·
        -- PRINCIPAL.  The right derivation introduced `∼χ ⋏ ∼ρ`, so both of its
        -- premises are in hand and the two cuts are legal at the strictly
        -- smaller ranks of `χ` and `ρ`.
        have heq : (ψ₁ ⋏ ψ₂) = ((∼χ) ⋏ (∼ρ)) := hcase
        obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp heq
        have hcχ : χ.complexity < r := by
          simp only [Semiformula.complexity_or] at hr; omega
        have hcρ : ρ.complexity < r := by
          simp only [Semiformula.complexity_or] at hr; omega
        have hd : BoundedDerivable r α ((χ ⋎ ρ) :: Γ₁) :=
          BoundedDerivable.or hα₀ hprem
        have hsubL : ∀ ζ : Proposition L, ((χ ⋎ ρ) :: Γ₁) ⊆ (χ ⋎ ρ) :: ζ :: Θ := by
          intro ζ x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssL hx
            simp only [List.mem_cons] at this
            tauto
        -- `A`: the left premise, with the cut formula scrubbed out of its own
        -- context.  This is the step the structural hypothesis cannot do.
        have hA : BoundedDerivable r (NONote.redOrd α₀ δ') (χ :: ρ :: Θ) :=
          ih2 α₀ δ' (lt_of_lt_of_le (NONote.nadd_lt_nadd_left δ' hα₀) hs) hprem hr
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
            (BoundedDerivable.and hlt₀ hlt₁ heP heQ)
            (by
              intro x hx
              have := hssR hx
              simp only [List.mem_cons] at this ⊢
              tauto)
        -- `B` and `C`: the two right premises, each against the whole left
        -- derivation.
        have hB : BoundedDerivable r (NONote.redOrd α δ₀) ((∼χ) :: Θ) :=
          ih2 α δ₀ (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₀) hs) hd hr
            (hsubL (∼χ)) heP
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hssR (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
        have hC : BoundedDerivable r (NONote.redOrd α δ₁) ((∼ρ) :: Θ) :=
          ih2 α δ₁ (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₁) hs) hd hr
            (hsubL (∼ρ)) heQ
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hssR (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
        have h₀ : NONote.nadd α₀ δ' < NONote.nadd α δ' :=
          NONote.nadd_lt_nadd_left δ' hα₀
        have h₁ : NONote.nadd α δ₁ < NONote.nadd α δ' :=
          NONote.nadd_lt_nadd_right α hlt₁
        have hAlt : NONote.redOrd α₀ δ' <
            NONote.mid (NONote.nadd α₀ δ') (NONote.nadd α δ₁) (NONote.nadd α δ') :=
          NONote.sq_lt_mid_left h₀ h₁
        have hClt : NONote.redOrd α δ₁ <
            NONote.mid (NONote.nadd α₀ δ') (NONote.nadd α δ₁) (NONote.nadd α δ') :=
          NONote.sq_lt_mid_right h₀ h₁
        have hMlt : NONote.mid (NONote.nadd α₀ δ') (NONote.nadd α δ₁) (NONote.nadd α δ') <
            NONote.redOrd α δ' :=
          NONote.mid_lt_sq h₀ h₁
        have hBlt : NONote.redOrd α δ₀ < NONote.redOrd α δ' :=
          NONote.redOrd_lt_right α hlt₀
        have hA' : BoundedDerivable r (NONote.redOrd α₀ δ') (ρ :: χ :: Θ) := by
          refine BoundedDerivable.contraction ?_ hA
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          tauto
        have step : BoundedDerivable r
            (NONote.mid (NONote.nadd α₀ δ') (NONote.nadd α δ₁) (NONote.nadd α δ'))
            (χ :: Θ) := by
          refine BoundedDerivable.contraction ?_
            (BoundedDerivable.cut hcρ hAlt hClt hA' hC)
          intro x hx
          simp only [List.cons_append, List.mem_cons, List.mem_append] at hx ⊢
          tauto
        refine BoundedDerivable.contraction ?_
          (BoundedDerivable.cut hcχ hMlt hBlt step hB)
        intro x hx
        simp only [List.mem_append] at hx
        tauto
      · have hmem : (ψ₁ ⋏ ψ₂) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have hsub : ∀ ζ : Proposition L, ζ :: Δ₁ ⊆ ∼(χ ⋎ ρ) :: ζ :: Θ := by
          intro ζ x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto
        have hsubL : ∀ ζ : Proposition L, Γ₁ ⊆ (χ ⋎ ρ) :: ζ :: Θ := by
          intro ζ x hx
          have := hssL hx
          simp only [List.mem_cons] at this ⊢
          tauto
        have kp := ihP hs₀ (χ := χ) (ρ := ρ) (Γ₁ := Γ₁) (Θ := ψ₁ :: Θ)
          hr hprem (hsubL ψ₁) (hsub ψ₁)
        have kq := ihQ hs₁ (χ := χ) (ρ := ρ) (Γ₁ := Γ₁) (Θ := ψ₂ :: Θ)
          hr hprem (hsubL ψ₂) (hsub ψ₂)
        exact drop_head
          (BoundedDerivable.and (NONote.redOrd_lt_right α hlt₀)
            (NONote.redOrd_lt_right α hlt₁) kp kq) hmem
  | @all δ' δ₀ ψ Δ₁ hlt _ ih =>
      intro hs χ ρ Γ₁ Θ hr hprem hssL hssR
      have hs' : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs)
      have hmem : (∀¹ ψ) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have hr' : ((Rewriting.shift χ) ⋎ (Rewriting.shift ρ)).complexity ≤ r := by
        simpa using hr
      have key := ih hs' (χ := Rewriting.shift χ) (ρ := Rewriting.shift ρ)
        (Γ₁ := Γ₁⁺) (Θ := ψ.free :: Θ⁺) hr' hprem.shift
        (by
          intro x hx
          simp only [Rewriting.shifts, List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := hssL hy
          simp only [List.mem_cons] at this ⊢
          rcases this with rfl | hm
          · left; rfl
          · right; right
            simp only [Rewriting.shifts, List.mem_map]
            exact ⟨y, hm, rfl⟩)
        (by
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp
          · simp only [Rewriting.shifts, List.mem_map] at hx
            obtain ⟨y, hy, rfl⟩ := hx
            have := hssR (List.mem_cons_of_mem _ hy)
            simp only [List.mem_cons] at this ⊢
            rcases this with rfl | hm
            · left; simp
            · right; right
              simp only [Rewriting.shifts, List.mem_map]
              exact ⟨y, hm, rfl⟩)
      exact drop_head (BoundedDerivable.all (NONote.redOrd_lt_right α hlt) key) hmem
  | @exs δ' δ₀ ψ Δ₁ t hlt _ ih =>
      intro hs χ ρ Γ₁ Θ hr hprem hssL hssR
      have hs' : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs)
      have hmem : (∃¹ ψ) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih hs' (χ := χ) (ρ := ρ) (Γ₁ := Γ₁) (Θ := ψ/[t] :: Θ) hr hprem
        (by
          intro x hx
          have := hssL hx
          simp only [List.mem_cons] at this ⊢
          tauto)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto)
      exact drop_head (BoundedDerivable.exs t (NONote.redOrd_lt_right α hlt) key) hmem
  | @cut δ' δ₀ δ₁ ψ Δ₁ Δ₂ hc hlt₀ hlt₁ hp hn ihp ihn =>
      intro hs χ ρ Γ₁ Θ hr hprem hssL hssR
      have hs₀ : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₀) hs)
      have hs₁ : NONote.nadd α δ₁ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₁) hs)
      have hsubL : ∀ ζ : Proposition L, Γ₁ ⊆ (χ ⋎ ρ) :: ζ :: Θ := by
        intro ζ x hx
        have := hssL hx
        simp only [List.mem_cons] at this ⊢
        tauto
      have kp := ihp hs₀ (χ := χ) (ρ := ρ) (Γ₁ := Γ₁) (Θ := ψ :: Θ)
        hr hprem (hsubL ψ)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_left _ hx)
            simp only [List.mem_cons] at this
            tauto)
      have kn := ihn hs₁ (χ := χ) (ρ := ρ) (Γ₁ := Γ₁) (Θ := ∼ψ :: Θ)
        hr hprem (hsubL (∼ψ))
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_right _ hx)
            simp only [List.mem_cons] at this
            tauto)
      refine BoundedDerivable.contraction ?_
        (BoundedDerivable.cut hc (NONote.redOrd_lt_right α hlt₀)
          (NONote.redOrd_lt_right α hlt₁) kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto

set_option maxHeartbeats 2000000 in
/-- Principal case for `⋏`: the left derivation ended by introducing the cut
formula `χ ⋏ ρ`, so it has two premises, and the right derivation, which
introduced `∼χ ⋎ ∼ρ`, has one that carries both disjuncts. -/
private theorem reduction_and {r : ℕ} {s α α₀ α₁ : NONote}
    (ih2 : RedIH2 L r s) (hα₀ : α₀ < α) (hα₁ : α₁ < α) :
    ∀ {δ : NONote} {Δ₀ : Sequent L}, BoundedDerivable r δ Δ₀ →
      NONote.nadd α δ ≤ s →
      ∀ {χ ρ : Proposition L} {Γ₁ Θ : Sequent L},
        (χ ⋏ ρ).complexity ≤ r →
        BoundedDerivable r α₀ (χ :: Γ₁) →
        BoundedDerivable r α₁ (ρ :: Γ₁) →
        Γ₁ ⊆ (χ ⋏ ρ) :: Θ →
        Δ₀ ⊆ ∼(χ ⋏ ρ) :: Θ →
          BoundedDerivable r (NONote.redOrd α δ) Θ := by
  intro δ Δ₀ he
  induction he with
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
  | @or δ' δ₀ ψ₁ ψ₂ Δ₁ hlt heP ih =>
      intro hs χ ρ Γ₁ Θ hr hp hq hssL hssR
      have hs' : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs)
      by_cases hcase : (ψ₁ ⋎ ψ₂) = ∼(χ ⋏ ρ)
      ·
        -- PRINCIPAL.
        have heq : (ψ₁ ⋎ ψ₂) = ((∼χ) ⋎ (∼ρ)) := hcase
        obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp heq
        have hcχ : χ.complexity < r := by
          simp only [Semiformula.complexity_and] at hr; omega
        have hcρ : ρ.complexity < r := by
          simp only [Semiformula.complexity_and] at hr; omega
        have hd : BoundedDerivable r α ((χ ⋏ ρ) :: Γ₁) :=
          BoundedDerivable.and hα₀ hα₁ hp hq
        have hsubR : ∀ ζ : Proposition L,
            (((∼χ) ⋎ (∼ρ)) :: Δ₁) ⊆ ∼(χ ⋏ ρ) :: ζ :: Θ := by
          intro ζ x hx
          have := hssR hx
          simp only [List.mem_cons] at this ⊢
          tauto
        have hsubL : (χ :: Γ₁) ⊆ (χ ⋏ ρ) :: χ :: Θ := by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssL hx
            simp only [List.mem_cons] at this
            tauto
        have hsubL' : (ρ :: Γ₁) ⊆ (χ ⋏ ρ) :: ρ :: Θ := by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssL hx
            simp only [List.mem_cons] at this
            tauto
        have hA₀ : BoundedDerivable r (NONote.redOrd α₀ δ') (χ :: Θ) :=
          ih2 α₀ δ' (lt_of_lt_of_le (NONote.nadd_lt_nadd_left δ' hα₀) hs) hp hr
            hsubL (BoundedDerivable.or hlt heP) (hsubR χ)
        have hA₁ : BoundedDerivable r (NONote.redOrd α₁ δ') (ρ :: Θ) :=
          ih2 α₁ δ' (lt_of_lt_of_le (NONote.nadd_lt_nadd_left δ' hα₁) hs) hq hr
            hsubL' (BoundedDerivable.or hlt heP) (hsubR ρ)
        have hB : BoundedDerivable r (NONote.redOrd α δ₀) ((∼χ) :: (∼ρ) :: Θ) :=
          ih2 α δ₀ (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs) hd hr
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
        have h₀ : NONote.nadd α₀ δ' < NONote.nadd α δ' :=
          NONote.nadd_lt_nadd_left δ' hα₀
        have hBs : NONote.nadd α δ₀ < NONote.nadd α δ' :=
          NONote.nadd_lt_nadd_right α hlt
        have hAlt : NONote.redOrd α₀ δ' <
            NONote.mid (NONote.nadd α₀ δ') (NONote.nadd α δ₀) (NONote.nadd α δ') :=
          NONote.sq_lt_mid_left h₀ hBs
        have hBlt : NONote.redOrd α δ₀ <
            NONote.mid (NONote.nadd α₀ δ') (NONote.nadd α δ₀) (NONote.nadd α δ') :=
          NONote.sq_lt_mid_right h₀ hBs
        have hMlt : NONote.mid (NONote.nadd α₀ δ') (NONote.nadd α δ₀) (NONote.nadd α δ') <
            NONote.redOrd α δ' :=
          NONote.mid_lt_sq h₀ hBs
        have hA₁lt : NONote.redOrd α₁ δ' < NONote.redOrd α δ' :=
          NONote.redOrd_lt_left δ' hα₁
        have step : BoundedDerivable r
            (NONote.mid (NONote.nadd α₀ δ') (NONote.nadd α δ₀) (NONote.nadd α δ'))
            ((∼ρ) :: Θ) := by
          refine BoundedDerivable.contraction ?_
            (BoundedDerivable.cut hcχ hAlt hBlt hA₀ hB)
          intro x hx
          simp only [List.mem_append, List.mem_cons] at hx ⊢
          tauto
        refine BoundedDerivable.contraction ?_
          (BoundedDerivable.cut hcρ hA₁lt hMlt hA₁ step)
        intro x hx
        simp only [List.mem_append] at hx
        tauto
      · have hmem : (ψ₁ ⋎ ψ₂) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have key := ih hs' (χ := χ) (ρ := ρ) (Γ₁ := Γ₁) (Θ := ψ₁ :: ψ₂ :: Θ) hr hp hq
          (by
            intro x hx
            have := hssL hx
            simp only [List.mem_cons] at this ⊢
            tauto)
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
        exact drop_head (BoundedDerivable.or (NONote.redOrd_lt_right α hlt) key) hmem
  | @and δ' δ₀ δ₁ ψ₁ ψ₂ Δ₁ hlt₀ hlt₁ heP heQ ihP ihQ =>
      intro hs χ ρ Γ₁ Θ hr hp hq hssL hssR
      have hs₀ : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₀) hs)
      have hs₁ : NONote.nadd α δ₁ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₁) hs)
      have hmem : (ψ₁ ⋏ ψ₂) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have hsub : ∀ ζ : Proposition L, ζ :: Δ₁ ⊆ ∼(χ ⋏ ρ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssR (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto
      have hsubL : ∀ ζ : Proposition L, Γ₁ ⊆ (χ ⋏ ρ) :: ζ :: Θ := by
        intro ζ x hx
        have := hssL hx
        simp only [List.mem_cons] at this ⊢
        tauto
      have kp := ihP hs₀ (χ := χ) (ρ := ρ) (Γ₁ := Γ₁) (Θ := ψ₁ :: Θ)
        hr hp hq (hsubL ψ₁) (hsub ψ₁)
      have kq := ihQ hs₁ (χ := χ) (ρ := ρ) (Γ₁ := Γ₁) (Θ := ψ₂ :: Θ)
        hr hp hq (hsubL ψ₂) (hsub ψ₂)
      exact drop_head
        (BoundedDerivable.and (NONote.redOrd_lt_right α hlt₀)
          (NONote.redOrd_lt_right α hlt₁) kp kq) hmem
  | @all δ' δ₀ ψ Δ₁ hlt _ ih =>
      intro hs χ ρ Γ₁ Θ hr hp hq hssL hssR
      have hs' : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs)
      have hmem : (∀¹ ψ) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have hr' : ((Rewriting.shift χ) ⋏ (Rewriting.shift ρ)).complexity ≤ r := by
        simpa using hr
      have key := ih hs' (χ := Rewriting.shift χ) (ρ := Rewriting.shift ρ)
        (Γ₁ := Γ₁⁺) (Θ := ψ.free :: Θ⁺) hr' hp.shift hq.shift
        (by
          intro x hx
          simp only [Rewriting.shifts, List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := hssL hy
          simp only [List.mem_cons] at this ⊢
          rcases this with rfl | hm
          · left; rfl
          · right; right
            simp only [Rewriting.shifts, List.mem_map]
            exact ⟨y, hm, rfl⟩)
        (by
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp
          · simp only [Rewriting.shifts, List.mem_map] at hx
            obtain ⟨y, hy, rfl⟩ := hx
            have := hssR (List.mem_cons_of_mem _ hy)
            simp only [List.mem_cons] at this ⊢
            rcases this with rfl | hm
            · left; simp
            · right; right
              simp only [Rewriting.shifts, List.mem_map]
              exact ⟨y, hm, rfl⟩)
      exact drop_head (BoundedDerivable.all (NONote.redOrd_lt_right α hlt) key) hmem
  | @exs δ' δ₀ ψ Δ₁ t hlt _ ih =>
      intro hs χ ρ Γ₁ Θ hr hp hq hssL hssR
      have hs' : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs)
      have hmem : (∃¹ ψ) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih hs' (χ := χ) (ρ := ρ) (Γ₁ := Γ₁) (Θ := ψ/[t] :: Θ) hr hp hq
        (by
          intro x hx
          have := hssL hx
          simp only [List.mem_cons] at this ⊢
          tauto)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto)
      exact drop_head (BoundedDerivable.exs t (NONote.redOrd_lt_right α hlt) key) hmem
  | @cut δ' δ₀ δ₁ ψ Δ₁ Δ₂ hc hlt₀ hlt₁ hpp hnn ihp ihn =>
      intro hs χ ρ Γ₁ Θ hr hp hq hssL hssR
      have hs₀ : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₀) hs)
      have hs₁ : NONote.nadd α δ₁ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₁) hs)
      have hsubL : ∀ ζ : Proposition L, Γ₁ ⊆ (χ ⋏ ρ) :: ζ :: Θ := by
        intro ζ x hx
        have := hssL hx
        simp only [List.mem_cons] at this ⊢
        tauto
      have kp := ihp hs₀ (χ := χ) (ρ := ρ) (Γ₁ := Γ₁) (Θ := ψ :: Θ)
        hr hp hq (hsubL ψ)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_left _ hx)
            simp only [List.mem_cons] at this
            tauto)
      have kn := ihn hs₁ (χ := χ) (ρ := ρ) (Γ₁ := Γ₁) (Θ := ∼ψ :: Θ)
        hr hp hq (hsubL (∼ψ))
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_right _ hx)
            simp only [List.mem_cons] at this
            tauto)
      refine BoundedDerivable.contraction ?_
        (BoundedDerivable.cut hc (NONote.redOrd_lt_right α hlt₀)
          (NONote.redOrd_lt_right α hlt₁) kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto

set_option maxHeartbeats 2000000 in
/-- Principal case for `∃`: the left derivation ended by introducing `∃¹ χ` with
some witness `t₀`, and the right derivation introduced `∀¹ ∼χ`.

This is the case that rules out the whole inversion-based strategy.  There is no
inversion for `∃` — the witness a derivation chose is not recoverable from its
conclusion — so the only way to line the two sides up is to take `t₀` from the
*left* premise and instantiate the right one at it, which the substitution lemma
does.

It is also the case that forces the symmetric measure.  The second cut premise
is the right premise instantiated at `t₀`, and it still carries `∼(∃¹ χ)` in its
own context; scrubbing that means running the reduction with the sides swapped,
at the pair `(δ₀, α)`, which is below `(α, δ)` only in the natural sum. -/
private theorem reduction_exs {r : ℕ} {s α α₀ : NONote}
    (ih2 : RedIH2 L r s) (hα₀ : α₀ < α) :
    ∀ {δ : NONote} {Δ₀ : Sequent L}, BoundedDerivable r δ Δ₀ →
      NONote.nadd α δ ≤ s →
      ∀ {χ : Semiproposition L 1} {t₀ : SyntacticTerm L} {Γ₁ Θ : Sequent L},
        (∃¹ χ).complexity ≤ r →
        BoundedDerivable r α₀ (χ/[t₀] :: Γ₁) →
        Γ₁ ⊆ (∃¹ χ) :: Θ →
        Δ₀ ⊆ ∼(∃¹ χ) :: Θ →
          BoundedDerivable r (NONote.redOrd α δ) Θ := by
  intro δ Δ₀ he
  induction he with
  | @identity δ' k rl v =>
      intro _ χ t₀ Γ₁ Θ _ _ _ hssR
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
      intro _ χ t₀ Γ₁ Θ _ _ _ hssR
      refine of_mem_verum ?_
      have h := hssR (show (⊤ : Proposition L) ∈ [(⊤ : Proposition L)] by simp)
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact absurd h (by simp)
      · exact h
  | @contraction δ' Δ' Δ ss _ ih =>
      intro hs χ t₀ Γ₁ Θ hr hprem hssL hssR
      exact ih hs hr hprem hssL (fun x hx => hssR (ss hx))
  | @or δ' δ₀ ψ₁ ψ₂ Δ₁ hlt _ ih =>
      intro hs χ t₀ Γ₁ Θ hr hprem hssL hssR
      have hs' : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs)
      have hmem : (ψ₁ ⋎ ψ₂) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih hs' (χ := χ) (t₀ := t₀) (Γ₁ := Γ₁) (Θ := ψ₁ :: ψ₂ :: Θ) hr hprem
        (by
          intro x hx
          have := hssL hx
          simp only [List.mem_cons] at this ⊢
          tauto)
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
      exact drop_head (BoundedDerivable.or (NONote.redOrd_lt_right α hlt) key) hmem
  | @and δ' δ₀ δ₁ ψ₁ ψ₂ Δ₁ hlt₀ hlt₁ _ _ ihP ihQ =>
      intro hs χ t₀ Γ₁ Θ hr hprem hssL hssR
      have hs₀ : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₀) hs)
      have hs₁ : NONote.nadd α δ₁ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₁) hs)
      have hmem : (ψ₁ ⋏ ψ₂) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have hsub : ∀ ζ : Proposition L, ζ :: Δ₁ ⊆ ∼(∃¹ χ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssR (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto
      have hsubL : ∀ ζ : Proposition L, Γ₁ ⊆ (∃¹ χ) :: ζ :: Θ := by
        intro ζ x hx
        have := hssL hx
        simp only [List.mem_cons] at this ⊢
        tauto
      have kp := ihP hs₀ (χ := χ) (t₀ := t₀) (Γ₁ := Γ₁) (Θ := ψ₁ :: Θ)
        hr hprem (hsubL ψ₁) (hsub ψ₁)
      have kq := ihQ hs₁ (χ := χ) (t₀ := t₀) (Γ₁ := Γ₁) (Θ := ψ₂ :: Θ)
        hr hprem (hsubL ψ₂) (hsub ψ₂)
      exact drop_head
        (BoundedDerivable.and (NONote.redOrd_lt_right α hlt₀)
          (NONote.redOrd_lt_right α hlt₁) kp kq) hmem
  | @all δ' δ₀ ψ Δ₁ hlt hpr ih =>
      intro hs χ t₀ Γ₁ Θ hr hprem hssL hssR
      have hs' : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs)
      by_cases hcase : (∀¹ ψ) = ∼(∃¹ χ)
      ·
        -- PRINCIPAL.
        have heq : (∀¹ ψ) = (∀¹ (∼χ)) := hcase
        obtain rfl := (Semiformula.all_inj _ _).mp heq
        have hcχ : (χ/[t₀] : Proposition L).complexity < r := by
          simp only [Semiformula.complexity_rew] at *
          simp only [Semiformula.complexity_exs] at hr
          omega
        have hd : BoundedDerivable r α ((∃¹ χ) :: Γ₁) :=
          BoundedDerivable.exs t₀ hα₀ hprem
        -- `A`: the left premise, scrubbed of the cut formula.
        have hA : BoundedDerivable r (NONote.redOrd α₀ δ') ((χ/[t₀] : Proposition L) :: Θ) :=
          ih2 α₀ δ' (lt_of_lt_of_le (NONote.nadd_lt_nadd_left δ' hα₀) hs) hprem hr
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hssL hx
                simp only [List.mem_cons] at this
                tauto)
            (BoundedDerivable.all hlt hpr)
            (by
              intro x hx
              have := hssR hx
              simp only [List.mem_cons] at this ⊢
              tauto)
        -- The right premise instantiated at the witness the *left* side chose.
        -- No inversion for `∃` is used, or exists.
        have hBsub : BoundedDerivable r δ₀ ((∼(χ/[t₀] : Proposition L)) :: Δ₁) := by
          have := all_premise_subst hpr t₀
          simpa using this
        -- `B`: that premise scrubbed, by running the reduction with the two
        -- sides swapped.  This is what the symmetric measure buys.
        have hswap : NONote.nadd δ₀ α < s := by
          rw [NONote.nadd_comm]
          exact lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs
        have hrneg : (∼(∃¹ χ) : Proposition L).complexity ≤ r := by simpa using hr
        have hB : BoundedDerivable r (NONote.redOrd δ₀ α)
            ((∼(χ/[t₀] : Proposition L)) :: Θ) :=
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
        have hAlt : NONote.redOrd α₀ δ' < NONote.redOrd α δ' :=
          NONote.redOrd_lt_left δ' hα₀
        have hBlt : NONote.redOrd δ₀ α < NONote.redOrd α δ' := by
          have : NONote.nadd δ₀ α < NONote.nadd α δ' := by
            rw [NONote.nadd_comm]
            exact NONote.nadd_lt_nadd_right α hlt
          exact NONote.sq_lt_sq this
        refine BoundedDerivable.contraction ?_
          (BoundedDerivable.cut hcχ hAlt hBlt hA hB)
        intro x hx
        simp only [List.mem_append] at hx
        tauto
      · have hmem : (∀¹ ψ) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have hr' : (∃¹ (Rewriting.shift χ)).complexity ≤ r := by simpa using hr
        -- `shift` and substitution commute, but only after the witness is
        -- shifted too; `Rew.shift_comp_subst1` is the exact form needed.
        have hcomm : (Rewriting.shift (χ/[t₀]) : Proposition L)
            = (Rewriting.shift χ)/[Rew.shift t₀] := by
          show Rew.shift ▹ (Rew.subst ![t₀] ▹ χ) = Rew.subst ![Rew.shift t₀] ▹ (Rew.shift ▹ χ)
          rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app,
            Rew.shift_comp_subst1]
        have hpremS : BoundedDerivable r α₀
            (((Rewriting.shift χ)/[Rew.shift t₀] : Proposition L) :: Γ₁⁺) := by
          have hk := hprem.shift
          simp only [Rewriting.shifts, List.map_cons] at hk ⊢
          rw [← hcomm]
          exact hk
        have key := ih hs' (χ := Rewriting.shift χ) (t₀ := Rew.shift t₀)
          (Γ₁ := Γ₁⁺) (Θ := ψ.free :: Θ⁺) hr' hpremS
          (by
            intro x hx
            simp only [Rewriting.shifts, List.mem_map] at hx
            obtain ⟨y, hy, rfl⟩ := hx
            have := hssL hy
            simp only [List.mem_cons] at this ⊢
            rcases this with rfl | hm
            · left; simp
            · right; right
              simp only [Rewriting.shifts, List.mem_map]
              exact ⟨y, hm, rfl⟩)
          (by
            intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · simp
            · simp only [Rewriting.shifts, List.mem_map] at hx
              obtain ⟨y, hy, rfl⟩ := hx
              have := hssR (List.mem_cons_of_mem _ hy)
              simp only [List.mem_cons] at this ⊢
              rcases this with rfl | hm
              · left; simp
              · right; right
                simp only [Rewriting.shifts, List.mem_map]
                exact ⟨y, hm, rfl⟩)
        exact drop_head (BoundedDerivable.all (NONote.redOrd_lt_right α hlt) key) hmem
  | @exs δ' δ₀ ψ Δ₁ t hlt _ ih =>
      intro hs χ t₀ Γ₁ Θ hr hprem hssL hssR
      have hs' : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs)
      have hmem : (∃¹ ψ) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih hs' (χ := χ) (t₀ := t₀) (Γ₁ := Γ₁) (Θ := ψ/[t] :: Θ) hr hprem
        (by
          intro x hx
          have := hssL hx
          simp only [List.mem_cons] at this ⊢
          tauto)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto)
      exact drop_head (BoundedDerivable.exs t (NONote.redOrd_lt_right α hlt) key) hmem
  | @cut δ' δ₀ δ₁ ψ Δ₁ Δ₂ hc hlt₀ hlt₁ _ _ ihp ihn =>
      intro hs χ t₀ Γ₁ Θ hr hprem hssL hssR
      have hs₀ : NONote.nadd α δ₀ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₀) hs)
      have hs₁ : NONote.nadd α δ₁ ≤ s :=
        le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₁) hs)
      have hsubL : ∀ ζ : Proposition L, Γ₁ ⊆ (∃¹ χ) :: ζ :: Θ := by
        intro ζ x hx
        have := hssL hx
        simp only [List.mem_cons] at this ⊢
        tauto
      have kp := ihp hs₀ (χ := χ) (t₀ := t₀) (Γ₁ := Γ₁) (Θ := ψ :: Θ)
        hr hprem (hsubL ψ)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_left _ hx)
            simp only [List.mem_cons] at this
            tauto)
      have kn := ihn hs₁ (χ := χ) (t₀ := t₀) (Γ₁ := Γ₁) (Θ := ∼ψ :: Θ)
        hr hprem (hsubL (∼ψ))
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_right _ hx)
            simp only [List.mem_cons] at this
            tauto)
      refine BoundedDerivable.contraction ?_
        (BoundedDerivable.cut hc (NONote.redOrd_lt_right α hlt₀)
          (NONote.redOrd_lt_right α hlt₁) kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto

set_option maxHeartbeats 2000000 in
/-- Principal case for `∀`: the left derivation ended by introducing `∀¹ χ`, and
the right derivation introduced `∃¹ ∼χ` with some witness `t`.

Mirror image of the existential case: the witness comes from the *right* premise
and the left premise is instantiated at it.  Again no inversion is used, and
again the second cut premise is produced by running the reduction with the sides
swapped.

The non-principal cases are written differently from the propositional lemmas,
and better.  They hand `ih2` the *whole* left derivation rather than its premise,
which matters in the right's `∀` case: that rule shifts the context, and
shifting a whole derivation is immediate, whereas shifting a premise of the form
`χ.free :: Γ⁺` is not — `free` and `shift` do not commute, they disagree about
where the fresh variable lands. -/
private theorem reduction_all {r : ℕ} {s α α₀ : NONote}
    (ih2 : RedIH2 L r s) (hα₀ : α₀ < α) :
    ∀ {δ : NONote} {Δ₀ : Sequent L}, BoundedDerivable r δ Δ₀ →
      NONote.nadd α δ ≤ s →
      ∀ {χ : Semiproposition L 1} {Γ₁ Θ : Sequent L},
        (∀¹ χ).complexity ≤ r →
        BoundedDerivable r α₀ (Semiformula.free χ :: Γ₁⁺) →
        Γ₁ ⊆ (∀¹ χ) :: Θ →
        Δ₀ ⊆ ∼(∀¹ χ) :: Θ →
          BoundedDerivable r (NONote.redOrd α δ) Θ := by
  intro δ Δ₀ he
  induction he with
  | @identity δ' k rl v =>
      intro _ χ Γ₁ Θ _ _ _ hssR
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
      intro _ χ Γ₁ Θ _ _ _ hssR
      refine of_mem_verum ?_
      have h := hssR (show (⊤ : Proposition L) ∈ [(⊤ : Proposition L)] by simp)
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact absurd h (by simp)
      · exact h
  | @contraction δ' Δ' Δ ss _ ih =>
      intro hs χ Γ₁ Θ hr hprem hssL hssR
      exact ih hs hr hprem hssL (fun x hx => hssR (ss hx))
  | @or δ' δ₀ ψ₁ ψ₂ Δ₁ hlt heP _ =>
      intro hs χ Γ₁ Θ hr hprem hssL hssR
      have hmem : (ψ₁ ⋎ ψ₂) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih2 α δ₀ (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs)
        (BoundedDerivable.all hα₀ hprem) hr (Θ := ψ₁ :: ψ₂ :: Θ)
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
      exact drop_head (BoundedDerivable.or (NONote.redOrd_lt_right α hlt) key) hmem
  | @and δ' δ₀ δ₁ ψ₁ ψ₂ Δ₁ hlt₀ hlt₁ heP heQ _ _ =>
      intro hs χ Γ₁ Θ hr hprem hssL hssR
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
      have kp := ih2 α δ₀ (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₀) hs)
        (BoundedDerivable.all hα₀ hprem) hr (Θ := ψ₁ :: Θ) (hsubL ψ₁) heP (hsubR ψ₁)
      have kq := ih2 α δ₁ (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₁) hs)
        (BoundedDerivable.all hα₀ hprem) hr (Θ := ψ₂ :: Θ) (hsubL ψ₂) heQ (hsubR ψ₂)
      exact drop_head
        (BoundedDerivable.and (NONote.redOrd_lt_right α hlt₀)
          (NONote.redOrd_lt_right α hlt₁) kp kq) hmem
  | @all δ' δ₀ ψ Δ₁ hlt hpr _ =>
      intro hs χ Γ₁ Θ hr hprem hssL hssR
      have hmem : (∀¹ ψ) ∈ Θ := by
        have h := hssR List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      -- Shift the whole left derivation.  This is the step that would be
      -- painful if the left premise were carried instead.
      have hdS : BoundedDerivable r α
          ((Rewriting.shift ((∀¹ χ : Proposition L))) :: Γ₁⁺) := by
        have hk := (BoundedDerivable.all hα₀ hprem).shift
        simpa only [Rewriting.shifts, List.map_cons] using hk
      have hrS : (Rewriting.shift ((∀¹ χ : Proposition L))).complexity ≤ r := by
        simpa using hr
      have key := ih2 α δ₀ (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs)
        hdS hrS (Θ := Semiformula.free ψ :: Θ⁺)
        (by
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp
          · simp only [Rewriting.shifts, List.mem_map] at hx
            obtain ⟨y, hy, rfl⟩ := hx
            have := hssL hy
            simp only [List.mem_cons] at this ⊢
            rcases this with rfl | hm
            · left; rfl
            · right; right
              simp only [Rewriting.shifts, List.mem_map]
              exact ⟨y, hm, rfl⟩)
        hpr
        (by
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp
          · simp only [Rewriting.shifts, List.mem_map] at hx
            obtain ⟨y, hy, rfl⟩ := hx
            have := hssR (List.mem_cons_of_mem _ hy)
            simp only [List.mem_cons] at this ⊢
            rcases this with rfl | hm
            · left; simp
            · right; right
              simp only [Rewriting.shifts, List.mem_map]
              exact ⟨y, hm, rfl⟩)
      exact drop_head (BoundedDerivable.all (NONote.redOrd_lt_right α hlt) key) hmem
  | @exs δ' δ₀ ψ Δ₁ t hlt hpr _ =>
      intro hs χ Γ₁ Θ hr hprem hssL hssR
      by_cases hcase : (∃¹ ψ) = ∼(∀¹ χ)
      ·
        -- PRINCIPAL.  The witness `t` is the right derivation's; the left
        -- premise is instantiated at it by the substitution lemma.
        have heq : (∃¹ ψ) = (∃¹ (∼χ)) := hcase
        obtain rfl : ψ = ∼χ := by simpa using heq
        have hcχ : ((χ/[t] : Proposition L)).complexity < r := by
          simp only [Semiformula.complexity_rew] at *
          simp only [Semiformula.complexity_all] at hr
          omega
        have hd : BoundedDerivable r α ((∀¹ χ) :: Γ₁) :=
          BoundedDerivable.all hα₀ hprem
        have hAprem : BoundedDerivable r α₀ ((χ/[t] : Proposition L) :: Γ₁) :=
          all_premise_subst hprem t
        have hA : BoundedDerivable r (NONote.redOrd α₀ δ')
            ((χ/[t] : Proposition L) :: Θ) :=
          ih2 α₀ δ' (lt_of_lt_of_le (NONote.nadd_lt_nadd_left δ' hα₀) hs) hAprem hr
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hssL hx
                simp only [List.mem_cons] at this
                tauto)
            (BoundedDerivable.exs t hlt hpr)
            (by
              intro x hx
              have := hssR hx
              simp only [List.mem_cons] at this ⊢
              tauto)
        have hBsub : BoundedDerivable r δ₀ ((∼(χ/[t] : Proposition L)) :: Δ₁) := by
          simpa using hpr
        have hswap : NONote.nadd δ₀ α < s := by
          rw [NONote.nadd_comm]
          exact lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs
        have hrneg : (∼(∀¹ χ) : Proposition L).complexity ≤ r := by simpa using hr
        have hB : BoundedDerivable r (NONote.redOrd δ₀ α)
            ((∼(χ/[t] : Proposition L)) :: Θ) :=
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
        have hAlt : NONote.redOrd α₀ δ' < NONote.redOrd α δ' :=
          NONote.redOrd_lt_left δ' hα₀
        have hBlt : NONote.redOrd δ₀ α < NONote.redOrd α δ' := by
          have hlt' : NONote.nadd δ₀ α < NONote.nadd α δ' := by
            rw [NONote.nadd_comm]
            exact NONote.nadd_lt_nadd_right α hlt
          exact NONote.sq_lt_sq hlt'
        refine BoundedDerivable.contraction ?_
          (BoundedDerivable.cut hcχ hAlt hBlt hA hB)
        intro x hx
        simp only [List.mem_append] at hx
        tauto
      · have hmem : (∃¹ ψ) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have key := ih2 α δ₀ (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt) hs)
          (BoundedDerivable.all hα₀ hprem) hr (Θ := ψ/[t] :: Θ)
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hssL hx
              simp only [List.mem_cons] at this
              tauto)
          hpr
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hssR (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto)
        exact drop_head (BoundedDerivable.exs t (NONote.redOrd_lt_right α hlt) key) hmem
  | @cut δ' δ₀ δ₁ ψ Δ₁ Δ₂ hc hlt₀ hlt₁ hpp hnn _ _ =>
      intro hs χ Γ₁ Θ hr hprem hssL hssR
      have hsubL : ∀ ζ : Proposition L, ((∀¹ χ) :: Γ₁) ⊆ (∀¹ χ) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssL hx
          simp only [List.mem_cons] at this
          tauto
      have kp := ih2 α δ₀ (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₀) hs)
        (BoundedDerivable.all hα₀ hprem) hr (Θ := ψ :: Θ) (hsubL ψ) hpp
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_left _ hx)
            simp only [List.mem_cons] at this
            tauto)
      have kn := ih2 α δ₁ (lt_of_lt_of_le (NONote.nadd_lt_nadd_right α hlt₁) hs)
        (BoundedDerivable.all hα₀ hprem) hr (Θ := ∼ψ :: Θ) (hsubL (∼ψ)) hnn
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_right _ hx)
            simp only [List.mem_cons] at this
            tauto)
      refine BoundedDerivable.contraction ?_
        (BoundedDerivable.cut hc (NONote.redOrd_lt_right α hlt₀)
          (NONote.redOrd_lt_right α hlt₁) kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto

/-! ### The reduction lemma itself -/

set_option maxHeartbeats 2000000 in
/-- The reduction lemma, in the form the well-founded recursion needs: the
measure `s` bounds the natural sum of the two ordinals. -/
private theorem reduction_aux {r : ℕ} :
    ∀ (s β γ : NONote), NONote.nadd β γ ≤ s →
      ∀ {Γ₀ : Sequent L}, BoundedDerivable r β Γ₀ →
        ∀ {φ : Proposition L}, φ.complexity ≤ r →
        ∀ {Θ Δ₀ : Sequent L}, Γ₀ ⊆ φ :: Θ →
          BoundedDerivable r γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ →
            BoundedDerivable r (NONote.redOrd β γ) Θ := by
  intro s
  induction s using WellFoundedLT.induction with
  | _ s ihs =>
    intro β γ hbg
    have ih2 : RedIH2 L r (NONote.nadd β γ) := fun β' γ' h =>
      ihs (NONote.nadd β' γ') (lt_of_lt_of_le h hbg) β' γ' le_rfl
    -- `contraction` leaves the ordinal alone, so the measure cannot dispose of
    -- it; only a structural induction on the left derivation can, and that
    -- induction carries the measure bound so the principal cases can hand it on.
    suffices K : ∀ (α : NONote) {Γ₀ : Sequent L}, BoundedDerivable r α Γ₀ →
        NONote.nadd α γ ≤ NONote.nadd β γ →
        ∀ {φ : Proposition L}, φ.complexity ≤ r →
        ∀ {Θ Δ₀ : Sequent L}, Γ₀ ⊆ φ :: Θ →
          BoundedDerivable r γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ →
            BoundedDerivable r (NONote.redOrd α γ) Θ by
      intro Γ₀ hd φ hφ Θ Δ₀ hss he hst
      exact K β hd le_rfl hφ hss he hst
    intro α Γ₀ hd
    induction hd with
    | @contraction α' Δ' Γ' ss _ ihprem =>
        intro hs φ hφ Θ Δ₀ hss he hst
        exact ihprem hs hφ (fun x hx => hss (ss hx)) he hst
    | @identity α' k rl v =>
        intro _ φ _ Θ Δ₀ hss he hst
        have hle : γ ≤ NONote.redOrd α' γ :=
          le_trans (NONote.le_nadd_right α' γ) (NONote.le_nadd_left _ _)
        have hp := hss (show Semiformula.rel rl v ∈
          [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
        have hn := hss (show Semiformula.nrel rl v ∈
          [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hn
        rcases hp with hpφ | hpΘ
        · -- the positive atom is the cut formula, so its dual heads the other
          -- side and already occurs in the target
          have hnΘ : (∼φ : Proposition L) ∈ Θ := by
            rcases hn with hnφ | hnΘ
            · exact absurd (hpφ.trans hnφ.symm) (by simp)
            · rw [← hpφ]; simpa using hnΘ
          exact (BoundedDerivable.contraction
            (fun x hx => by
              have := hst hx
              simp only [List.mem_cons] at this
              rcases this with rfl | hm
              · exact hnΘ
              · exact hm) he).mono_ord hle
        · rcases hn with hnφ | hnΘ
          · have hpΘ' : (∼φ : Proposition L) ∈ Θ := by
              rw [← hnφ]; simpa using hpΘ
            exact (BoundedDerivable.contraction
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
        · -- the cut formula is `⊤`, so the other side carries a `⊥`, which no
          -- rule introduces and which can therefore be dropped
          have hbot : Δ₀ ⊆ (⊥ : Proposition L) :: Θ := by
            intro x hx
            have := hst hx
            simp only [List.mem_cons] at this ⊢
            rcases this with rfl | hm
            · left; rw [← hφ]; simp
            · tauto
          exact (drop_falsum he hbot).mono_ord
            (le_trans (NONote.le_nadd_right α' γ) (NONote.le_nadd_left _ _))
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
          have hs' : NONote.nadd α₀ γ ≤ NONote.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_left γ hb) hs)
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
          exact drop_head (BoundedDerivable.or (NONote.redOrd_lt_left γ hb) key) hmem
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
          have hs1 : NONote.nadd α₀ γ ≤ NONote.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_left γ hb1) hs)
          have hs2 : NONote.nadd α₁ γ ≤ NONote.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_left γ hb2) hs)
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
            (BoundedDerivable.and (NONote.redOrd_lt_left γ hb1)
              (NONote.redOrd_lt_left γ hb2) kp kq) hmem
    | @all α' α₀ χ Γ' hb hprem ihp =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (∀¹ χ) = φ
        · subst hcase
          exact reduction_all ih2 hb he hs hφ hprem
            (fun x hx => hss (List.mem_cons_of_mem _ hx)) hst
        · have hmem : (∀¹ χ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          have hs' : NONote.nadd α₀ γ ≤ NONote.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_left γ hb) hs)
          -- the rule shifts its context, so the cut formula shifts with it
          have hφ' : (Rewriting.shift φ).complexity ≤ r := by simpa using hφ
          have key := ihp hs' hφ' (Θ := Semiformula.free χ :: Θ⁺)
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · simp only [Rewriting.shifts, List.mem_map] at hx
                obtain ⟨y, hy, rfl⟩ := hx
                have := hss (show y ∈ (∀¹ χ) :: Γ' by simp only [List.mem_cons]; tauto)
                simp only [List.mem_cons] at this
                rcases this with rfl | hm
                · left; rfl
                · right; right
                  simp only [Rewriting.shifts, List.mem_map]
                  exact ⟨y, hm, rfl⟩)
            he.shift
            (by
              intro x hx
              simp only [Rewriting.shifts, List.mem_map] at hx
              obtain ⟨y, hy, rfl⟩ := hx
              have := hst hy
              simp only [List.mem_cons] at this ⊢
              rcases this with rfl | hm
              · left; simp
              · right; right
                simp only [Rewriting.shifts, List.mem_map]
                exact ⟨y, hm, rfl⟩)
          exact drop_head (BoundedDerivable.all (NONote.redOrd_lt_left γ hb) key) hmem
    | @exs α' α₀ χ Γ' t hb hprem ihp =>
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
          have hs' : NONote.nadd α₀ γ ≤ NONote.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_left γ hb) hs)
          have key := ihp hs' hφ (Θ := χ/[t] :: Θ)
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
            (BoundedDerivable.exs t (NONote.redOrd_lt_left γ hb) key) hmem
    | @cut α' α₀ α₁ χ Γ₁ Γ₂ hc hb1 hb2 hpp hnn ihp ihn =>
        intro hs φ hφ Θ Δ₀ hss he hst
        have hs1 : NONote.nadd α₀ γ ≤ NONote.nadd β γ :=
          le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_left γ hb1) hs)
        have hs2 : NONote.nadd α₁ γ ≤ NONote.nadd β γ :=
          le_of_lt (lt_of_lt_of_le (NONote.nadd_lt_nadd_left γ hb2) hs)
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
        refine BoundedDerivable.contraction ?_
          (BoundedDerivable.cut hc (NONote.redOrd_lt_left γ hb1)
            (NONote.redOrd_lt_left γ hb2) kp kn)
        intro x hx
        simp only [List.mem_append] at hx
        tauto

/-- **Reduction.**  Two derivations that cut against each other on a formula of
complexity at most `r` combine into one that uses only cuts of complexity below
`r`.

The ordinal is `(β ⊕ γ) ⊕ (β ⊕ γ)` rather than the textbook `β ⊕ γ`.  The
propositional principal cases perform two *nested* cuts, the second taking the
first's result as a premise, so they need two strictly increasing ordinals above
everything the induction hypotheses return, and the natural sum alone supplies
only one.  Doubling repairs it and survives the recursion; the elimination
lemma will not notice, because `ω ^ α` is additively indecomposable. -/
theorem reduction {r : ℕ} (β γ : NONote) {Γ₀ Δ₀ Θ : Sequent L} {φ : Proposition L}
    (hφ : φ.complexity ≤ r)
    (hd : BoundedDerivable r β Γ₀) (hss : Γ₀ ⊆ φ :: Θ)
    (he : BoundedDerivable r γ Δ₀) (hst : Δ₀ ⊆ ∼φ :: Θ) :
    BoundedDerivable r (NONote.redOrd β γ) Θ :=
  reduction_aux (NONote.nadd β γ) β γ le_rfl hd hφ hss he hst

end BoundedDerivable

end OrdinalAnalysis
