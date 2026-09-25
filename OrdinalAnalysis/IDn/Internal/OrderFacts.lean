/-
  The internal order facts of the multi-level ϑ-notation, discharged: an instance of the
  hypothesis structure `IDn.Upper.InternalOrderFacts` of `IDn/UpperAux.lean`.

  The formulas are those of the coding: `x ≺ y` is `iltb x y = 1` (`thLtDef`), the normal form
  and the domain condition are `thNFDef` and `thDomDef` of `IDn/Internal/Order.lean`, the
  descending lists are `isSL` (`isSLDef`), and the concatenation is `iapp`
  (`IDn/Internal/JumpList.lean`).  Every field of `OrderAxioms` is one lemma of
  `IDn/Internal/{Order,OrderT,OrderE,JumpList}.lean`, in every model of `IΣ₁`
  (`orderAxioms_coded`).
-/
import OrdinalAnalysis.IDn.Internal.JumpList
import OrdinalAnalysis.IDn.UpperAux

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.ID1.Internal (bor band beq bor_eq_one band_eq_one beq_eq_one)

/-- `x ≺ y` on codes. -/
def thLtDef : 𝚺₁.Semisentence 2 := .mkSigma “x y. !iltbDef 1 x y”

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem eval_thLtDef (x y : V) : thLtDef.val.Evalb ![x, y] ↔ iltb x y = 1 := by
  simp [thLtDef, iltb_defined.iff, eq_comm]

@[simp] theorem eval_isSLDef (s : V) : isSLDef.val.Evalb ![s] ↔ isSL s := by
  simp [isSLDef, isSL, isDom, sumK_defined.iff, nfA_defined.iff, isDomb_defined.iff, eq_comm]

/-- U2's exponent list `Upper.itoL` is `expList`. -/
theorem itoL_eq_expList (c : V) : Upper.itoL c = expList c := rfl

end Model

/-- **Every field of `OrderAxioms`**, for the predicates of the coding, in every model of
`IΣ₁`. -/
theorem orderAxioms_coded (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    Upper.OrderAxioms V (fun x y => iltb x y = 1) isNF isDom isSL iapp where
  lt_mc := iltb_mc
  nf_mc := isNF_mc
  dom_mc := isDom_mc
  lt_trans := fun ha hb hc hab hbc =>
    iltb_trans (isTerm_of_isNF ha) (isTerm_of_isNF hb) (isTerm_of_isNF hc) hab hbc
  not_lt_zero := not_iltb_zero_right
  lt_Omega_Omega := iltb_Omega_Omega_iff
  lt_Omega_theta := iltb_Omega_theta_iff
  lt_theta_Omega := iltb_theta_Omega_iff
  lt_theta_theta := fun _ _ _ b ha _ => iltb_theta_theta_iff' b (isTerm_of_isNF ha)
  lt_cons_Omega := fun x s j => by rw [iltb_cons_prin x s (Or.inl (kind_tcOmega j))]
  lt_cons_theta := fun x s j b => by rw [iltb_cons_prin x s (Or.inr (kind_tcTheta j b))]
  lt_Omega_cons := fun i y t => by
    rw [iltb_prin_cons (Or.inl (kind_tcOmega i)), bor_eq_one, beq_eq_one]
  lt_theta_cons := fun i a y t => by
    rw [iltb_prin_cons (Or.inr (kind_tcTheta i a)), bor_eq_one, beq_eq_one]
  lt_cons_cons := fun x s y t => by
    rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
  nf_isTerm := fun _ h => isTerm_of_isNF h
  nf_theta := isNF_tcTheta_iff
  dom_theta := fun k a _ => isDom_tcTheta_iff k a
  fld_cons := isNF_isDom_tcCons_iff
  fld_of_iinE := fun k g c hc hd h =>
    ⟨isNF_of_iinE k g c (nfA_of_isNF hc) h, isDom_of_iinE k g c hd h⟩
  fld_of_iinG := fun k y c hc hd h =>
    ⟨isNF_of_iinG k y c (nfA_of_isNF hc) h, isDom_of_iinG k y c hd h⟩
  sl_zero := isSL_zero
  sl_cons := isSL_cons_iff
  sl_shape := fun _ hs => isSL_shape hs
  app_zero := iapp_zero_left
  app_isnoc := fun s y w _ => iapp_isnocL y w s
  sl_isnoc_of_app := fun s z w h => isSL_isnocL_of_isSL_iapp z w s h
  sl_app_right := fun s r h => isSL_of_isSL_iapp_right r s h
  iinE_app_right := fun k g s r _ h => iinE_iapp_right k g r s h
  lt_isnoc_cases := fun _ _ _ hs hz h => iltb_isnocL_cases hs hz h
  lt_itoL_iff := fun _ _ hb _ hc _ => by
    rw [itoL_eq_expList, itoL_eq_expList]; exact iltb_expList_iff hb hc

/-- **The internal order facts, discharged**: the `Σ₁` formulas of the coding satisfy
`OrderAxioms` in every model of `IΣ₁`. -/
noncomputable def codedOrderFacts : Upper.InternalOrderFacts where
  ltDef := thLtDef
  nfDef := thNFDef
  domDef := thDomDef
  slDef := isSLDef
  app := iapp
  appDef := iappDef
  app_defined := iapp_defined
  axioms := fun V _ _ => by
    have e1 : (fun x y : V => thLtDef.val.Evalb ![x, y]) = fun x y => iltb x y = 1 := by
      funext x y; exact propext (eval_thLtDef x y)
    have e2 : (fun x : V => thNFDef.val.Evalb ![x]) = isNF := by
      funext x; exact propext (eval_thNFDef x)
    have e3 : (fun x : V => thDomDef.val.Evalb ![x]) = isDom := by
      funext x; exact propext (eval_thDomDef x)
    have e4 : (fun x : V => isSLDef.val.Evalb ![x]) = isSL := by
      funext x; exact propext (eval_isSLDef x)
    rw [e1, e2, e3, e4]
    exact orderAxioms_coded V

end OrdinalAnalysis.IDn.Internal
