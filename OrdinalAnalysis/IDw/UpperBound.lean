/-
  The upper bound of the analysis of `ID_ω`: transfinite induction along the multi-level ϑ-order
  up to every notation below `Ω₁` is provable in `IDw WFormWc`.

  Source: T. Arai, *Lectures on ordinal analysis*, arXiv:2304.00246, §1.6, and W. Buchholz and
  W. Pohlers, J. Symbolic Logic 43 (1978), pp. 121–123 (`σ = ω`); the `ID_n` version is
  `IDn/UpperBound.lean`.  The sentence `TI_a(≺, X)` is `tiUptoSentence` of `IDw/TISentence.lean`
  (`Prog(≺, X) → ∀x (x ≺ ⌜a⌝ → X x)`, `≺` the internal order on normal domain codes,
  `X` the free predicate of `LXJ`).

  **The proof** (`upper_bound_models`), in an arbitrary arithmetically standard model `N` of
  `IDw WFormWc` (`WModel.of_models`): a notation `a` below `Ω₁` lies below some
  `ϑ₀(ω_m(Ω_ω + 1))` (`exists_lt_tower`), the code of which is `ϑ₀(τ_m)` (`mc_omegaTower`) and
  is in `J(0, ·)` (`W_theta_tau`, BP78 Theorems 2 and 3), so every `x ≺ ⌜a⌝` of the field is in
  `J(0, ·)` (`W_down`), and the induction scheme of level `0` at the free predicate `X` turns
  `Prog(≺, X)` into `J(0, ·) ⊆ X`.  Completeness (`Lift.provable_of_models`) gives the provability
  `upper_bound`.

  Contrary to `ID_n` no level bound enters: `Ω_ω` bounds every level, so the tower
  `ω_m(Ω_ω + 1)` is cofinal in the countable notations outright.
-/
import OrdinalAnalysis.IDw.WellOrderingTau
import OrdinalAnalysis.IDw.UpperAuxCof
import OrdinalAnalysis.IDw.TISentence

set_option autoImplicit false

namespace OrdinalAnalysis.IDw.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.IDw.Internal
open ThetaVNoteD (omegaTower)

/-! ### The concrete order formulas -/

section Formulas

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The field of `orderFormulas` is `fldW`. -/
theorem fld_orderFormulas (x : V) : orderFormulas.fld x ↔ fldW x := by
  unfold OrderFormulas.fld OrderFormulas.nf OrderFormulas.dom fldW
  show thNFDef.val.Evalb ![x] ∧ thDomDef.val.Evalb ![x] ↔ _
  rw [eval_thNFDef, eval_thDomDef]

/-- The order of `orderFormulas` is `iltb x y = 1`. -/
theorem lt_orderFormulas (x y : V) : orderFormulas.lt x y ↔ iltb x y = 1 :=
  eval_iltDef x y

/-! ### The towers as codes -/

/-- **The tower `τ_m` is the code of `ω_m(Ω_ω + 1)`.** -/
theorem mc_omegaTower (m : ℕ) :
    mc (V := V) (omegaTower m (ThetaVNoteD.OmegaW + ThetaVNoteD.one)).1 = tauW m := by
  induction m with
  | zero =>
    rw [ThetaVNoteD.omegaTower_zero, omegaW_add_one_val, mc_cons, mc_cons, mc_OmegaW, mc_nil]
    rfl
  | succ m ih =>
    rw [omegaTower_succ_val, mc_cons, ih, mc_nil]
    rfl

end Formulas

/-! ### The upper bound -/

/-- **The upper bound**: for every notation `a ≺ Ω₁`, `IDw WFormWc` proves transfinite induction
for the free predicate `X` up to `a`, `TI_a(≺, X)` of `IDw/TISentence.lean`. -/
theorem upper_bound {a : ThetaVNoteD} (ha : a.1 < ThetaVTerm.Omega 0) :
    IDw WFormWc ⊢ tiUptoSentence orderFormulas a := by
  apply Lift.provable_of_models
  intro N _ s _ hN
  have hI : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := Lift.models_iSigma₁ WFormWc
  have hM : WModel N := WModel.of_models
  rw [models_iff, eval_tiUpto]
  intro hprog x hx
  obtain ⟨hxf, -, hxlt⟩ := hx
  obtain ⟨m, hm⟩ := exists_lt_tower ha
  have hlt : iltb (mc (V := N) a.1) (tcTheta 0 (tauW m)) = 1 := by
    have := (iltb_mc (V := N) a.1 _).mpr hm
    rwa [mc_theta, mc_omegaTower, Nat.cast_zero] at this
  have hxlt' : iltb x (mc (V := N) a.1) = 1 := (lt_orderFormulas _ _).mp hxlt
  have hxD : DkW (0 : N) x := ⟨(fld_orderFormulas x).mp hxf, fun j hj => absurd hj (by simp)⟩
  have hJ0 : Jm (0 : N) x :=
    W_down hM (W_theta_tau hM m) hxD
      (iltb_trans (isTerm_of_fldW hxD.1) (isTerm_mc a.1)
        (isTerm_of_fldW (tauW_facts (s := s) m).2.2) hxlt' hlt)
  refine hM.ind 0 Lift.definable_xmem (fun z hA => ?_) x hJ0
  obtain ⟨hzD, -, hacc⟩ := hA
  exact hprog z fun y hy _ hyz => hacc y ⟨(fld_orderFormulas y).mp hy, fun j hj => absurd hj (by simp)⟩
    ((lt_orderFormulas _ _).mp hyz)

end OrdinalAnalysis.IDw.Upper
