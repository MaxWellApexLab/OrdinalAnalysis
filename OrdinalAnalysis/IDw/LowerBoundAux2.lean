/- Source: OrdinalAnalysis/IDn/LowerBoundAux2.lean (`fieldInI0`, `provable_fieldInI0_of_ti`, `codeAt0_mem_stageSetN_iff`; hand port: the free predicate is read by the formula `θ(x) :≡ x ≺ ⌜Ω₁⌝ → J(0, x)`, `IDw/LowerBoundAux.lean`). -/

/-
  Second helper for the lower bound of `ID_ω` (`IDw/LowerBound.lean`): from `TI_{Ω₁}(≺, X)` to
  the level-`0` accessible part, and the level-`0` stages of `WFormWc`.

  Source: `OrdinalAnalysis.IDn.LowerBoundAux2` (from `ID1.LowerBound.provable_fieldInI_of_ti` and
  `ID1.StageSem.codeNote_mem_stageSet_acc`), adapted to the uniform form of `ID_ω`.

  **Step 1 (`X := θ`).**  In `IDn` the free predicate `X` is reinterpreted as the level-`0`
  predicate `I_0`, and `Prog(≺, X)` becomes literally the closure axiom of `I_0`.  In `ID_ω` the
  closure axiom at level `y = 0` carries the extra conjunct `x ≺ Ω₁` (`WFormW`: `A(y, x) :≡
  D(y, x) ∧ x ≺ Ω_{y+1} ∧ ∀z (D(y, z) ∧ z ≺ x → P z)`), so `X` is read by the *relativised* formula

      θ(x)  :≡  x ≺ ⌜Ω₁⌝ → J(0, x)                                     (`thetaX`),

  for which `Prog(≺, θ)` still follows from the closure axiom at level `0`, using only the
  transitivity of the internal order (`prog_thetaX`).  With the bound `a = Ω₁` of the sentence
  the relativisation disappears again: `TI_{Ω₁}(≺, θ)` says `∀x (x ≺ ⌜Ω₁⌝ → J(0, x))`
  (`fieldInJ0`), and `IDw WFormWc ⊢ TI_{Ω₁}(≺, X)` gives `IDw WFormWc ⊢ fieldInJ0`
  (`provable_fieldInJ0_of_ti`, through `xStruc` of `IDw/LowerBoundAux.lean` and completeness for
  the arithmetically standard models, `Lift.provable_of_models`).

  **Step 6 (the accessible part at level `0`).**  `codeAt0_mem_stageSetN_iff` computes the
  level-`0` stages of `WFormWc`: the code of `β : ThetaVNoteD` enters the stage `b : StageAt 0`
  exactly when `β < b.1`.

  Contents.

    `fieldInJ0`, `thetaX`                        **`∀x (x ≺ ⌜Ω₁⌝ → J(0, x))`**, the reading of `X`
    `prog_thetaX`                                `Prog(≺, θ)` from the closure axiom at level `0`
    `provable_fieldInJ0_of_ti`                   **`TI_{Ω₁}(≺, X) ⊢ ∀x (x ≺ ⌜Ω₁⌝ → J(0, x))`**
    `mem_opA_zero_iff`                           the operator of level `0`, read in `ℕ`
    `codeAt0_mem_stageSetN_iff`                  **the accessible part at level `0`**
-/
import OrdinalAnalysis.IDw.LowerBoundAux
import OrdinalAnalysis.IDw.StageSemantics
import OrdinalAnalysis.IDw.TISentence
import OrdinalAnalysis.IDw.Internal.OrderBridge
import Foundation.FirstOrder.Completeness

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.IDw.Upper
open OrdinalAnalysis.IDw.Internal (code tcOmega mc mc_nat mc_Omega thNFDef thDomDef isNF isDom isTerm_of_isNF iltb iltb_trans)
open OrdinalAnalysis.IDw.Lift (ArithStd Jmem)

/-! ### The sentence `∀x (x ≺ ⌜Ω₁⌝ → J(0, x))` and the reading of `X` -/

section Reread

/-- **`θ(x) :≡ x ≺ ⌜Ω₁⌝ → J(0, x)`**: the formula by which the free predicate `X` is read. -/
def thetaX : Semisentence LXJ 1 :=
  lm (belowC orderFormulas (ThetaVNoteD.Omega 0)) 🡒 Jat ((0 : ℕ) : Semiterm LXJ Empty 1) #0

/-- **`∀x (x ≺ ⌜Ω₁⌝ → J(0, x))`**: the field below `Ω₁` lies in the level-`0` accessible part. -/
def fieldInJ0 : Sentence LXJ := ∀¹ thetaX

section Model

variable {N : Type} [ORingStructure N] [s : Structure LXJ N] [ArithStd N]

omit [ArithStd N] in
theorem lMap_zero_numeral {ξ : Type*} {n : ℕ} :
    Semiterm.lMap toLXJ ((0 : ℕ) : Semiterm ℒₒᵣ ξ n) = ((0 : ℕ) : Semiterm LXJ ξ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral, Semiterm.Operator.Zero.term_eq]

/-- The numeral `0` denotes `0`. -/
theorem val_zero_numeral {ξ : Type*} {n : ℕ} (e : Fin n → N) (f : ξ → N) :
    Semiterm.val (s := s) e f ((0 : ℕ) : Semiterm LXJ ξ n) = 0 := by
  rw [← lMap_zero_numeral, Lift.val_lMap]
  simp [Semiterm.val_operator]

variable [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **`θ` in `N`**: `x ≺ ⌜Ω₁⌝ → J(0, x)`. -/
theorem eval_thetaX (x : N) :
    Semiformula.Eval (s := s) ![x] Empty.elim thetaX ↔
      (orderFormulas.fld x ∧ orderFormulas.fld (mc (V := N) (ThetaVTerm.Omega 0)) ∧
          orderFormulas.lt x (mc (V := N) (ThetaVTerm.Omega 0)) → Jmem (s := s) 0 x) := by
  unfold thetaX
  rw [LogicalConnective.HomClass.map_imply, Lift.eval_JatN, lm, Lift.eval_lMap]
  refine imp_congr (eval_belowC (F := orderFormulas) (N := N) (ThetaVNoteD.Omega 0) x) ?_
  rw [val_zero_numeral]
  exact Iff.rfl

theorem fld_iff_isNF_isDom (x : N) : orderFormulas.fld x ↔ isNF x ∧ isDom x :=
  and_congr (Internal.eval_thNFDef x) (Internal.eval_thDomDef x)

theorem lt_iff_iltb (x y : N) : orderFormulas.lt x y ↔ iltb x y = 1 := eval_iltDef x y

theorem mc_Omega_zero : mc (V := N) (ThetaVTerm.Omega 0) = tcOmega (0 : N) := by
  simp

/-- **`Prog(≺, θ)` from the closure axiom at level `0`**: the closure axiom of `WFormWc` at
`y = 0` reads `D_0(x) ∧ x ≺ Ω₁ ∧ (∀z ∈ D_0, z ≺ x → J(0, z)) → J(0, x)`, and `D_0(z)` is just
`fld z`; `θ z` follows from `z ≺ x ≺ Ω₁` by the transitivity of `≺`. -/
theorem prog_thetaX (hclos : Semiformula.Eval (s := s) ![] Empty.elim (closureAxJ WFormWc)) :
    ∀ x : N, (∀ y, orderFormulas.fld y → orderFormulas.fld x → orderFormulas.lt y x →
        Semiformula.Eval (s := s) ![y] Empty.elim thetaX) →
      Semiformula.Eval (s := s) ![x] Empty.elim thetaX := by
  intro x hprog
  rw [eval_thetaX]
  rintro ⟨hfx, hfΩ, hxΩ⟩
  rw [mc_Omega_zero] at hfΩ hxΩ
  have hxΩ' : iltb x (tcOmega (0 : N)) = 1 := (lt_iff_iltb _ _).mp hxΩ
  have hfx' := (fld_iff_isNF_isDom x).mp hfx
  have hfΩ' := (fld_iff_isNF_isDom _).mp hfΩ
  refine Upper.closure_c_of_eval (s := s) ArithStd.lMap_eq hclos 0 x ⟨⟨hfx', fun j hj => absurd hj (by simp)⟩, hxΩ', ?_⟩
  intro z hz hzx
  have hfz : orderFormulas.fld z := (fld_iff_isNF_isDom z).mpr hz.1
  have hzx' : orderFormulas.lt z x := (lt_iff_iltb _ _).mpr hzx
  have hzΩ : iltb z (tcOmega (0 : N)) = 1 :=
    iltb_trans (isTerm_of_isNF hz.1.1) (isTerm_of_isNF hfx'.1) (isTerm_of_isNF hfΩ'.1) hzx hxΩ'
  have := (eval_thetaX z).mp (hprog z hfz hfx hzx')
  rw [mc_Omega_zero] at this
  exact this ⟨hfz, hfΩ, (lt_iff_iltb _ _).mpr hzΩ⟩

/-- **`TI_{Ω₁}(≺, X)` gives `∀x (x ≺ ⌜Ω₁⌝ → J(0, x))`** (the analogue of
`IDn.provable_fieldInI0_of_ti`): in every arithmetically standard model of `IDw WFormWc` the
free predicate may be read by `θ` (`eval_of_provable_xStruc`); `Prog(≺, θ)` holds
(`prog_thetaX`), and `TI_{Ω₁}(≺, θ)` is `∀x (x ≺ ⌜Ω₁⌝ → θ x)`, i.e. `fieldInJ0`. -/
theorem provable_fieldInJ0_of_ti
    (h : IDw WFormWc ⊢ tiUptoSentence orderFormulas (ThetaVNoteD.Omega 0)) :
    IDw WFormWc ⊢ fieldInJ0 := by
  refine Lift.provable_of_models WFormWc fun N _ s _ hN => ?_
  refine models_iff.mpr ?_
  have hM : ∀ σ ∈ IDw WFormWc, Semiformula.Eval (s := s) ![] Empty.elim σ :=
    fun σ hσ => models_iff.mp (Semantics.modelsSet_iff.mp hN hσ)
  have hS : s.lMap toLXJ = Arithmetic.standardModel N := ArithStd.lMap_eq
  have hIS : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := Lift.models_iSigma₁ WFormWc
  have h1 := eval_of_provable_xStruc s thetaX WFormWc hS hM h
  have h2 := (@eval_tiUpto orderFormulas N _ (xStruc s thetaX)
    (@ArithStd.mk N _ (xStruc s thetaX) (xStruc_arithStd s thetaX hS)) hIS (ThetaVNoteD.Omega 0)).mp h1
  have hprog := prog_thetaX (s := s) (hM _ (closureAxJ_mem_IDw WFormWc))
  have h3 := h2 hprog
  refine (Semiformula.eval_all (s := s)).mpr fun x => ?_
  have e : (x :> ![] : Fin 1 → N) = ![x] := rfl
  rw [e, eval_thetaX]
  intro hx
  have := (eval_thetaX (s := s) x).mp (h3 x hx)
  exact this hx

end Model

end Reread

/-! ### The level-`0` stages of `WFormWc` -/

section Acc

open StageSem

/-- The `LForm`-structure of the stage semantics is that of `Upper.formStr`. -/
theorem formStruc_eq (T : Set ℕ) (Qr : ℕ → ℕ → Prop) :
    formStruc T Qr = formStr (N := ℕ) (fun t => t ∈ T) Qr := by
  have h : StageSem.pqStruc T Qr = Upper.pqStruc (N := ℕ) (fun t => t ∈ T) Qr := by
    refine Structure.ext (funext₃ fun k f v => ?_) (funext₃ fun k r v => ?_)
    · exact PEmpty.elim f
    · cases r <;> rfl
  unfold formStruc formStr
  rw [h]

/-- **The operator of level `0` of `WFormWc`, read in `ℕ`**: `x ∈ Γ_0(T)` iff `x` is in the field,
`x ≺ Ω₁`, and every field element below `x` is in `T` (no lower levels to see). -/
theorem mem_opA_zero_iff (T : Set ℕ) (L : ℕ → Set ℕ) (x : ℕ) :
    x ∈ opA WFormWc 0 T L ↔
      orderFormulas.fld x ∧ orderFormulas.lt x (code (ThetaVTerm.Omega 0)) ∧
        ∀ z : ℕ, orderFormulas.fld z → orderFormulas.lt z x → z ∈ T := by
  show Semiformula.Eval (s := formStruc T (fun j t => j < 0 ∧ t ∈ L j)) ![x, 0]
    Empty.elim WFormWc ↔ _
  rw [formStruc_eq, WFormWc, eval_WFormW]
  have hlt : ∀ y z : ℕ, iltDefW.val.Evalb ![y, z] ↔ orderFormulas.lt y z := fun y z => by
    rw [eval_iltDefW]; exact (eval_iltDef y z).symm
  have hd : ∀ (Qr : ℕ → ℕ → Prop) (x : ℕ),
      DcR Qr thNFDef thDomDef 0 x ↔ orderFormulas.fld x := fun Qr x =>
    ⟨fun h => h.1, fun h => ⟨h, fun j hj => absurd hj (Nat.not_lt_zero j)⟩⟩
  have hom : (tcOmega (0 : ℕ) : ℕ) = code (ThetaVTerm.Omega 0) := by
    have := mc_Omega (V := ℕ) 0
    rw [mc_nat] at this
    simpa using this.symm
  unfold AccR LtR
  rw [hom]
  exact and_congr (hd _ _) (and_congr (hlt _ _) (forall_congr' fun z =>
    imp_congr (hd _ _) (imp_congr (hlt _ _) Iff.rfl)))

/-- **The stages of the accessible part of level `0`, for `WFormWc`** (the analogue of
`IDn.codeAt0_mem_stageSetN_iff` and `ID1.StageSem.codeNote_mem_stageSet_acc`): the code of a
normal domain term `β` enters the stage `a : StageAt 0` exactly when `β ≺ a`. -/
theorem codeAt0_mem_stageSetN_iff (a : StageAt 0) (β : ThetaVNoteD) :
    (code β.1 : ℕ) ∈ stageSetN WFormWc (⟨0, a⟩ : Stage) ↔ β < a.1 := by
  induction a using WellFoundedLT.induction generalizing β with
  | _ a ih =>
  rw [mem_stageSetN_iff WFormWc a]
  have hunfold : ∀ (g : StageAt 0) (x : ℕ),
      x ∈ opA WFormWc 0 (stageSetN WFormWc (⟨0, g⟩ : Stage))
          (fun j => stageSetN WFormWc (Stage.top j)) ↔
        orderFormulas.fld x ∧ orderFormulas.lt x (code (ThetaVTerm.Omega 0)) ∧
          ∀ z : ℕ, orderFormulas.fld z → orderFormulas.lt z x →
            z ∈ stageSetN WFormWc (⟨0, g⟩ : Stage) :=
    fun g x => mem_opA_zero_iff _ _ x
  constructor
  · rintro ⟨g, hga, hg⟩
    rw [hunfold] at hg
    by_contra hβa
    have hgβ : g.1 < β := lt_of_lt_of_le hga (not_lt.mp hβa)
    have hmem := hg.2.2 (code g.1.1) ((Internal.eval_fld_iff g.1.1).mpr g.1.2)
      ((Internal.eval_lt_iff_lt g.1.1 β.1).mpr hgβ)
    exact lt_irrefl g.1 ((ih g hga g.1).mp hmem)
  · intro hβa
    refine ⟨⟨β, le_trans (le_of_lt hβa) a.2⟩, hβa, ?_⟩
    rw [hunfold]
    refine ⟨(Internal.eval_fld_iff β.1).mpr β.2, ?_, ?_⟩
    · exact (Internal.eval_lt_iff_lt β.1 (ThetaVNoteD.Omega 0).1).mpr (lt_of_lt_of_le hβa a.2)
    · intro z hz hzlt
      obtain ⟨t, ht⟩ := Internal.fld_surj z hz
      have hty : t.1 < β.1 := (Internal.eval_lt_iff_lt t.1 β.1).mp (by rw [ht]; exact hzlt)
      have := (ih ⟨β, le_trans (le_of_lt hβa) a.2⟩ hβa t).mpr hty
      rwa [ht] at this

end Acc

end IDw

end OrdinalAnalysis
