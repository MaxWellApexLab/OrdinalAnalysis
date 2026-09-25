/-
  The upper bound of the analysis of `ID_n`: transfinite induction along the multi-level
  ϑ-order up to every notation below `c_n = ϑ₀(ϑ_n 0)` is provable in `ID_n` for the
  well-ordering forms, and up to every countable notation in `ID_{<ω}`.

  Source: T. Arai, *Lectures on ordinal analysis*, arXiv:2304.00246, §1.6, level by level
  (`IDn/WellOrdering.lean`); the internal order is the hypothesis `F : OrderFormulas`.

  **The sentence.**  For a notation `a`, with `≺ = precW F` (the internal order on normal
  domain codes) and the free predicate `X`,

      TI_a(≺, X)  :≡  Prog(≺, X) → ∀x (x ≺ ⌜a⌝ → X x)          (`tiUptoSentence F ι a`),

  the shape of `ID1/UpperBound.tiUptoSentence`, in the language `LXIN ι`.

  **The proof** (`upper_bound_ID`), in an arbitrary arithmetically standard model of `ID A`
  whose levels `0, …, n` carry the forms (completeness, `Lift.provable_of_models`): by the sharp
  cofinality `a ≺ c_{n+1} ⇒ a ≺ ϑ₀(ω_m(Ω_{n+1} + 1))` (`exists_lt_theta0_tower`) and
  `ϑ₀(τ_m) ∈ I_0` (`WellOrdering.W_theta_tau`), every `x ≺ ⌜a⌝` is in `I_0`; the induction
  scheme of `I_0` at `X` turns `Prog(≺, X)` into `I_0 ⊆ X`.
-/
import OrdinalAnalysis.IDn.WellOrdering
import OrdinalAnalysis.IDn.UpperAuxCof

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.IDn.Internal OrdinalAnalysis.IDn.Lift InternalOrderFacts
open ThetaWNoteD (omegaTower)

/-! ### The sentences -/

section Sentences

variable (F : OrderFormulas) (ι : Type)

/-- `y ≺ x` (on the field) in `LXIN ι`, slot `0` the smaller element. -/
def precL : Semisentence (LXIN ι) 2 := lm (OrderFormulas.precW F)

/-- `x ≺ ⌜a⌝` in arithmetic. -/
def belowC (a : ThetaWNoteD) : Semisentence ℒₒᵣ 1 :=
  OrderFormulas.precW F ⇜ ![#0, ((code a.1 : ℕ) : Semiterm ℒₒᵣ Empty 1)]

/-- `Prog(≺, X) :≡ ∀x ((∀y ≺ x, X y) → X x)`. -/
def progX : Sentence (LXIN ι) :=
  ∀¹ ((∀¹ (precL F ι 🡒 Xat #0)) 🡒 Xat #0)

/-- **`TI_a(≺, X) :≡ Prog(≺, X) → ∀x (x ≺ ⌜a⌝ → X x)`**: transfinite induction for the free
predicate `X` along the multi-level ϑ-order up to `a`. -/
def tiUptoSentence (a : ThetaWNoteD) : Sentence (LXIN ι) :=
  progX F ι 🡒 ∀¹ (lm (belowC F a) 🡒 Xat #0)

end Sentences

/-! ### The sentences in an arithmetically standard structure -/

section Eval

variable {F : OrderFormulas} {ι : Type}
variable {N : Type} [ORingStructure N] [s : Structure (LXIN ι) N] [ArithStd ι N]
  [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eval_belowC (a : ThetaWNoteD) (x : N) :
    Semiformula.Evalb (M := N) ![x] (belowC F a) ↔
      F.fld x ∧ F.fld (mc (V := N) a.1) ∧ F.lt x (mc (V := N) a.1) := by
  unfold belowC
  rw [Semiformula.eval_substs]
  have e : (Semiterm.val (M := N) ![x] Empty.elim ∘
      ![(#0 : Semiterm ℒₒᵣ Empty 1), ((code a.1 : ℕ) : Semiterm ℒₒᵣ Empty 1)])
        = ![x, mc (V := N) a.1] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => k.elim0) j
      simp [numeral_eq_natCast, mc]
  rw [e]
  exact OrderFormulas.eval_precWDef F x _

omit [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- **`Prog(≺, X)` in `N`.** -/
theorem eval_progX :
    Semiformula.Eval (s := s) ![] Empty.elim (progX F ι) ↔
      ∀ x : N, (∀ y, F.fld y → F.fld x → F.lt y x → Xmem (s := s) y) → Xmem (s := s) x := by
  unfold progX
  rw [Semiformula.eval_all]
  refine forall_congr' fun x => ?_
  rw [LogicalConnective.HomClass.map_imply, Semiformula.eval_all, eval_XatN]
  refine imp_congr (forall_congr' fun y => ?_) Iff.rfl
  rw [LogicalConnective.HomClass.map_imply, eval_XatN, precL, eval_lm s ArithStd.lMap_eq]
  have e : (y :> x :> ![] : Fin 2 → N) = ![y, x] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    rfl
  rw [e]
  show (F.precWDef.val.Evalb ![y, x] → _) ↔ _
  rw [OrderFormulas.eval_precWDef]
  constructor
  · intro h hy hx hlt; exact h ⟨hy, hx, hlt⟩
  · rintro h ⟨hy, hx, hlt⟩; exact h hy hx hlt

/-- **`TI_a(≺, X)` in `N`.** -/
theorem eval_tiUpto (a : ThetaWNoteD) :
    Semiformula.Eval (s := s) ![] Empty.elim (tiUptoSentence F ι a) ↔
      ((∀ x : N, (∀ y, F.fld y → F.fld x → F.lt y x → Xmem (s := s) y) → Xmem (s := s) x) →
        ∀ x : N, F.fld x ∧ F.fld (mc (V := N) a.1) ∧ F.lt x (mc (V := N) a.1) →
          Xmem (s := s) x) := by
  unfold tiUptoSentence
  rw [LogicalConnective.HomClass.map_imply, eval_progX, Semiformula.eval_all]
  refine imp_congr Iff.rfl (forall_congr' fun x => ?_)
  rw [LogicalConnective.HomClass.map_imply, eval_XatN, eval_lm s ArithStd.lMap_eq]
  exact imp_congr (eval_belowC a x) Iff.rfl

end Eval

/-! ### The towers as codes -/

section Bridge

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The tower `τ_m` is the code of `ω_m(Ω_{n+1} + 1)`.** -/
theorem mc_omegaTower (n m : ℕ) :
    mc (V := V) (omegaTower m (ThetaWNoteD.Omega n + ThetaWNoteD.one)).1 = tau n m := by
  induction m with
  | zero =>
    rw [ThetaWNoteD.omegaTower_zero, omega_add_one_val, mc_cons, mc_cons, mc_Omega, mc_nil]
    rfl
  | succ m ih =>
    rw [omegaTower_succ_val, mc_cons, ih, mc_nil]
    rfl

end Bridge

/-! ### The upper bound -/

/-- **The upper bound, for any index type**: if the levels `0, …, n` of `ID A` (read through an
index map injective on them) carry the well-ordering forms, then `ID A` proves transfinite
induction up to every notation below `c_{n+1}`. -/
theorem upper_bound_ID (hJ : InternalOrderFacts) {ι : Type} [DecidableEq ι] (ix : ℕ → ι)
    (n : ℕ) (A : ι → Semisentence (LXIN ι) 1)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ix i = ix j → i = j)
    (hform : ∀ k, k ≤ n → A (ix k) = wForm hJ.toOrderFormulas ix k)
    {a : ThetaWNoteD} (ha : a < ThetaWNoteD.c (n + 1)) :
    ID A ⊢ tiUptoSentence hJ.toOrderFormulas ι a := by
  apply provable_of_models A
  intro N _ _ _ hN
  have := hN
  have : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_iSigma₁ A
  have hG : Good hJ ix n A := ⟨hinj, hform⟩
  rw [models_iff, eval_tiUpto]
  intro hprog x hx
  obtain ⟨m, hm⟩ := exists_lt_theta0_tower ha
  have hlt : hJ.lt (mc (V := N) a.1) (tcTheta 0 (tau n m)) := by
    have := (hJ.ax.lt_mc (V := N) a.1 _).mpr hm
    rwa [mc_theta, mc_omegaTower, Nat.cast_zero] at this
  obtain ⟨hτ, -, -, hGτ⟩ := tau_facts (hJ := hJ) (N := N) n m
  have hfτ : hJ.fld (tcTheta (0 : N) (tau (N := N) n m)) :=
    (fld_theta_iff _ _).mpr ⟨hτ, fun y h => absurd h (hGτ _ y)⟩
  have hW : W ix 0 x :=
    W_down hG (Nat.zero_le n) (W_theta_tau hG m) hfτ hx.1
      (lt_trans hx.1 hx.2.1 hfτ hx.2.2 hlt)
  exact W_induction hG (Nat.zero_le n) definable_xmem
    (fun x _ _ ih => hprog x fun y hy _ hyx => ih y hy hyx) x hW hx.1

end OrdinalAnalysis.IDn.Upper
