/-
  The new axiom of `PA + TI(ε₀)`, and its derivation in the ω-calculus.

  `paLX₁` is `paLX` together with one sentence: transfinite induction along
  the coded Veblen ordering `≺₁` restricted below the code of `ε₀`,

      TI₀ :≡ Prog(≺₁, X) → ∀ x ≺₁ ε₀̄, X x.

  The lower bound cuts every axiom of the theory out of a replayed proof, so
  it needs a cut-free derivation of `TI₀` — and, since the whole argument is
  a height count, at a height below `ε₁`.  The derivation is the climb of
  `ClimbVeblen.lean` collected by the ω-rule:

  * for each `k`, if `k ≺₁ ε₀̄` then `k` codes a notation `o < ε₀` and the
    climb gives `¬Prog, X(k̄)` at `height o < ε₀`; otherwise `∼(k̄ ≺₁ ε₀̄)` is
    derivable at `K₁ < ε₀`;
  * the ω-rule collects these at height `ε₀`, and one `or` rule at `ε₀ + 1`
    forms the axiom.

  So `TI₀` is derivable at height `ε₀ + 1 < ε₁`.  This is the converse of the
  boundedness lemma one level up, and the reason `ε₀` is the right cut-off:
  the ω-rule takes the supremum of the climbs to the notations below `ε₀`,
  which is `ε₀`.
-/
import OrdinalAnalysis.Gentzen.ClimbVeblen

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace OrdinalAnalysis.Gentzen.Epsilon1Axiom

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.StandardLX (trueArithLits stdLX)
open OrdinalAnalysis.Gentzen.LowerSyntax OrdinalAnalysis.Gentzen.LowerClass
open OrdinalAnalysis.Gentzen.Evaluate OrdinalAnalysis.Gentzen.EvInst
open OrdinalAnalysis.Gentzen.LowerClassEv
open OrdinalAnalysis.Gentzen.CodedVeblen OrdinalAnalysis.Gentzen.VNoteBridge
open OrdinalAnalysis.Gentzen.Climb OrdinalAnalysis.Gentzen.ClimbVeblen
open OrdinalAnalysis.Gamma0Note

/-! ### The axiom -/

/-- The closed `PA[X]` numeral for a Veblen notation. -/
def gamma0Term (a : Gamma0Note) : Semiterm LX ℕ 0 := ((gamma0Code a : ℕ) : Semiterm LX ℕ 0)

theorem gamma0Term_eq (a : Gamma0Note) : gamma0Term a = numLX (gamma0Code a) := rfl

@[simp] theorem freeVariables_gamma0Term (a : Gamma0Note) :
    (gamma0Term a).freeVariables = ∅ := by
  rw [gamma0Term_eq]; simp

/-- **The new axiom**: `TI(≺₁ ↾ ε₀)`, as a sentence. -/
def TI₀ : Sentence LX := (TIupto precCode₁ (gamma0Term (epsilonNote 0))).univCl

/-- **`PA[X] + TI(ε₀)`.** -/
def paLX₁ : Theory LX := insert TI₀ paLX

theorem mem_paLX₁ {σ : Sentence LX} : σ ∈ paLX₁ ↔ σ = TI₀ ∨ σ ∈ paLX :=
  Set.mem_insert_iff

/-! ### Its shape -/

theorem freeVariables_TIupto₁ (a : Gamma0Note) :
    (TIupto precCode₁ (gamma0Term a)).freeVariables = ∅ :=
  freeVariables_TIupto freeVariables_precCode₁ (freeVariables_gamma0Term a)

/-- `univCl` is a typing wrapper on the closed formula `TIupto precCode₁ ε₀̄`. -/
theorem emb_TI₀ :
    (Rewriting.emb TI₀ : Proposition LX) = TIupto precCode₁ (gamma0Term (epsilonNote 0)) := by
  have h : ((TIupto precCode₁ (gamma0Term (epsilonNote 0))).univCl : Proposition LX)
      = (TIupto precCode₁ (gamma0Term (epsilonNote 0))).univCl' :=
    Semiformula.coe_univCl_eq_univCl' _
  rw [show (Rewriting.emb TI₀ : Proposition LX)
        = ((TIupto precCode₁ (gamma0Term (epsilonNote 0))).univCl : Proposition LX) from rfl,
    h, Semiformula.univCl'_eq_self_of _ (freeVariables_TIupto₁ _)]

/-- The body of `TIupto precCode₁ n̄` is `belowBody gamma0Order n`: the shift of
a numeral is the numeral. -/
theorem TIupto_body_eq (n : ℕ) :
    (∼(precAt precCode₁ (#0 : Semiterm LX ℕ 1) (Rew.bShift (numLX n)))
        ⋎ Xat (#0 : Semiterm LX ℕ 1))
      = belowBody gamma0Order n := by
  simp only [numLX, rew_numeral]
  rfl

/-- **The evaluated axiom.** -/
theorem ev_TIupto₁ (a : Gamma0Note) :
    ev (TIupto precCode₁ (gamma0Term a))
      = ev (∼(Prog precCode₁)) ⋎ (∀¹ (ev (belowBody gamma0Order (gamma0Code a)))) := by
  rw [TIupto, ev_or, ev_all, gamma0Term_eq, TIupto_body_eq]

/-! ### The derivation -/

/-- The code of `ε₀`. -/
def n₀ : ℕ := gamma0Code (epsilonNote 0)

/-- **The ω-premises.**  For each `k`, the `k`-th instance of the body of the
axiom is derivable together with `¬Prog(≺₁)`, at some height below `ε₀`. -/
theorem premise (k : ℕ) : ∃ β : Gamma0Note, β < epsilonNote 0 ∧
    D β (evInst.inst (ev (belowBody gamma0Order n₀)) k :: [ev (∼(Prog precCode₁))]) := by
  rw [inst_belowBody, ev_precOrXat_eq]
  by_cases hk : precN₁ k n₀
  · obtain ⟨o, rfl⟩ := (precN₁_dom hk).1
    have ho : o < epsilonNote 0 := lt_of_precN₁_code hk
    refine ⟨OrdinalNotation.succ (veblenClimb.height o), ?_, ?_⟩
    · exact nadd_lt_epsilon (height_lt_epsilon0 ho) (one_lt_epsilon 0)
    · refine OmegaDerivable.or (OrdinalNotation.lt_succ _) ?_
      refine OmegaDerivable.contraction ?_ (veblenClimb.code o)
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
  · refine ⟨OrdinalNotation.succ K₁, ?_, ?_⟩
    · exact nadd_lt_epsilon K₁_lt_epsilon0 (one_lt_epsilon 0)
    · refine OmegaDerivable.or (OrdinalNotation.lt_succ _) ?_
      refine OmegaDerivable.contraction ?_ (veblenClimb.neg_precAt hk)
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl
      exact Or.inl rfl

/-- **The axiom is derivable at height `ε₀ + 1`.** -/
theorem TI₀_derivable_at :
    D (OrdinalNotation.succ (epsilonNote 0)) [ev (Rewriting.emb TI₀ : Proposition LX)] := by
  rw [emb_TI₀, ev_TIupto₁]
  refine OmegaDerivable.or (OrdinalNotation.lt_succ _) ?_
  choose β hβ using premise
  have h : D (epsilonNote 0)
      [∀¹ (ev (belowBody gamma0Order n₀)), ev (∼(Prog precCode₁))] :=
    OmegaDerivable.omegaRule β (fun k => (hβ k).1) (fun k => (hβ k).2)
  refine OmegaDerivable.contraction ?_ h
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  rcases hx with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem succ_epsilon0_lt_epsilon1 :
    OrdinalNotation.succ (epsilonNote 0) < epsilonNote 1 :=
  nadd_lt_epsilon (epsilon_lt_epsilon Gamma0Note.zero_lt_one) (one_lt_epsilon 1)

/-- **The new axiom is cut-free derivable below `ε₁`.** -/
theorem TI₀_derivable : ∃ β : Gamma0Note, β < epsilonNote 1 ∧
    OmegaDerivable trueArithLits evInst 0 β [ev (Rewriting.emb TI₀ : Proposition LX)] :=
  ⟨_, succ_epsilon0_lt_epsilon1, TI₀_derivable_at⟩

end OrdinalAnalysis.Gentzen.Epsilon1Axiom
