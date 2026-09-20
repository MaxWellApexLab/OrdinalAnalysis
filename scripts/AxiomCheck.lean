/-
  The axiom gate.

  Run with

      lake env lean scripts/AxiomCheck.lean

  Every headline theorem must print exactly

      [propext, Classical.choice, Quot.sound]

  The `#guard_msgs` wrappers make that a build failure rather than something a
  reader has to eyeball, so this file fails loudly if a `sorry`, an `axiom`, or
  a `native_decide` ever creeps into the chain.

  This file is expected to elaborate.  If it stops elaborating -- because a
  module was renamed, say -- that is itself the failure, and the gate must be
  repaired rather than skipped.
-/
import OrdinalAnalysis

open OrdinalAnalysis

/-! ### Ordinal notations -/

/-- info: 'OrdinalAnalysis.nadd_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.nadd_comm

/-- info: 'OrdinalAnalysis.NONote.nadd_lt_omegaPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.NONote.nadd_lt_omegaPow

/-! ### The finitary calculus -/

/-- info: 'OrdinalAnalysis.BoundedDerivable.reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.BoundedDerivable.reduction

/-- info: 'OrdinalAnalysis.BoundedDerivable.elimination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.BoundedDerivable.elimination

/-- info: 'OrdinalAnalysis.BoundedDerivable.cutElimination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.BoundedDerivable.cutElimination

/-- info: 'OrdinalAnalysis.BoundedDerivable.cutFree_of_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.BoundedDerivable.cutFree_of_derivation

/-! ### The infinitary calculus -/

/-- info: 'OrdinalAnalysis.OmegaDerivable.reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.OmegaDerivable.reduction

/-- info: 'OrdinalAnalysis.OmegaDerivable.elimination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.OmegaDerivable.elimination

/-- info: 'OrdinalAnalysis.OmegaDerivable.cutElimination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.OmegaDerivable.cutElimination

/-! ### Further results -/

/-- info: 'OrdinalAnalysis.nadd_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.nadd_assoc

/-- info: 'OrdinalAnalysis.NONote.lt_omegaPow_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.NONote.lt_omegaPow_self

/-- info: 'OrdinalAnalysis.BoundedDerivable.inv_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.BoundedDerivable.inv_all

/-! ### Gentzen's jump -/

/-- info: 'OrdinalAnalysis.Gentzen.jump_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.jump_A

/-- info: 'OrdinalAnalysis.Gentzen.jump_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.jump_B

/-- info: 'OrdinalAnalysis.Gentzen.OmegaCover.iadd_omegaPow_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.OmegaCover.iadd_omegaPow_cover

/-- info: 'OrdinalAnalysis.Gentzen.OmegaCover.arithmetic_omegaCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.OmegaCover.arithmetic_omegaCover

/-- info: 'OrdinalAnalysis.Gentzen.OmegaCover.concrete_omegaCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.OmegaCover.concrete_omegaCover

/-- info: 'OrdinalAnalysis.Gentzen.OmegaCover.concrete_jump_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.OmegaCover.concrete_jump_A

/-- info: 'OrdinalAnalysis.Gentzen.OmegaCover.concrete_jump_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.OmegaCover.concrete_jump_B

/-! ### Finite omega towers -/

/--
info: 'OrdinalAnalysis.Gentzen.OmegaTower.arithmetic_tower_omegaPow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.OmegaTower.arithmetic_tower_omegaPow

/-- info: 'OrdinalAnalysis.Gentzen.OmegaTower.concrete_tower_omegaPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.OmegaTower.concrete_tower_omegaPow

/-- info: 'OrdinalAnalysis.Gentzen.OmegaTower.concrete_tower_ti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.OmegaTower.concrete_tower_ti

/-- info: 'OrdinalAnalysis.Gentzen.OmegaTower.concrete_tower_TIupto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.OmegaTower.concrete_tower_TIupto

/-! ### External/internal notation bridge -/

/-- info: 'OrdinalAnalysis.Gentzen.NotationBridge.icmp_modelCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.NotationBridge.icmp_modelCode

/-- info: 'OrdinalAnalysis.Gentzen.NotationBridge.isNF_modelCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.NotationBridge.isNF_modelCode

/--
info: 'OrdinalAnalysis.Gentzen.NotationBridge.lt_iff_icmp_modelCode_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.NotationBridge.lt_iff_icmp_modelCode_eq_zero

/-- info: 'OrdinalAnalysis.Gentzen.NotationBridge.isNF_nonoteModelCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.NotationBridge.isNF_nonoteModelCode

/--
info: 'OrdinalAnalysis.Gentzen.NotationBridge.nonote_lt_iff_icmpModelCode_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.NotationBridge.nonote_lt_iff_icmpModelCode_eq_zero

/-! ### Coded order and cofinality -/

/-- info: 'OrdinalAnalysis.Gentzen.Order.arithmetic_precTrans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Order.arithmetic_precTrans

/-- info: 'OrdinalAnalysis.Gentzen.Order.concrete_precTrans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Order.concrete_precTrans

/-- info: 'OrdinalAnalysis.Gentzen.Order.concrete_tiUpto_downward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Order.concrete_tiUpto_downward

/-- info: 'OrdinalAnalysis.Gentzen.Cofinality.code_onoteTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Cofinality.code_onoteTower

/-- info: 'OrdinalAnalysis.Gentzen.Cofinality.exists_lt_nonoteTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Cofinality.exists_lt_nonoteTower

/-! ### Gentzen's upper bound -/

/-- info: 'OrdinalAnalysis.Gentzen.UpperBound.arithmetic_nonote_prec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.UpperBound.arithmetic_nonote_prec

/-- info: 'OrdinalAnalysis.Gentzen.UpperBound.concrete_nonote_prec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.UpperBound.concrete_nonote_prec

/-- info: 'OrdinalAnalysis.Gentzen.UpperBound.concrete_nonote_ti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.UpperBound.concrete_nonote_ti

/-- info: 'OrdinalAnalysis.Gentzen.UpperBound.concrete_nonote_TIupto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.UpperBound.concrete_nonote_TIupto

/-- info: 'OrdinalAnalysis.Gentzen.UpperBound.gentzen_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.UpperBound.gentzen_upper_bound

/-! ### Coding of notations -/

/-- info: 'OrdinalAnalysis.Gentzen.NotationBridge.code_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.NotationBridge.code_injective

/-- info: 'OrdinalAnalysis.Gentzen.NotationBridge.instEncodableONote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.NotationBridge.instEncodableONote

/-- info: 'OrdinalAnalysis.Gentzen.NotationBridge.ltb_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.NotationBridge.ltb_iff

/-- info: 'OrdinalAnalysis.Gentzen.NotationBridge.nfb_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.NotationBridge.nfb_iff

/-- info: 'OrdinalAnalysis.Gentzen.noteNumeral_eq_lMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.noteNumeral_eq_lMap

/-! ### The toy instance: transfinite induction along `<` in `PA[X]` -/

/-- info: 'OrdinalAnalysis.Gentzen.ToyOmega.toy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.ToyOmega.toy

/-- info: 'OrdinalAnalysis.Gentzen.ToyOmega.prog_implies_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.ToyOmega.prog_implies_below

/-! ### Syntax of the lower-bound target -/

/-- info: 'OrdinalAnalysis.Gentzen.LowerSyntax.emb_univCl_TI_precCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.LowerSyntax.emb_univCl_TI_precCode

/-- info: 'OrdinalAnalysis.Gentzen.LowerSyntax.neg_Prog' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.LowerSyntax.neg_Prog

/-- info: 'OrdinalAnalysis.Gentzen.LowerSyntax.complexity_TI_precCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.LowerSyntax.complexity_TI_precCode

/-! ### The standard structure on the extended language, and the atomic axioms -/

/-- info: 'OrdinalAnalysis.Gentzen.StandardLX.trueArithLits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.StandardLX.trueArithLits

/-- info: 'OrdinalAnalysis.Gentzen.StandardLX.eval_of_trueArithLits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.StandardLX.eval_of_trueArithLits

/-- info: 'OrdinalAnalysis.Gentzen.StandardLX.stdLX_lMap_toLX' depends on axioms: [propext] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.StandardLX.stdLX_lMap_toLX

/-! ### The coded ordering on standard codes -/

/-- info: 'OrdinalAnalysis.Gentzen.PrecStandard.precN_code_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.PrecStandard.precN_code_iff

/-- info: 'OrdinalAnalysis.Gentzen.PrecStandard.eval_precAt_numeral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.PrecStandard.eval_precAt_numeral

/-! ### The lower-bound formula class and closed-term evaluation -/

/-- info: 'OrdinalAnalysis.Gentzen.LowerClass.InC.exhaustive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.LowerClass.InC.exhaustive

/-- info: 'OrdinalAnalysis.Gentzen.LowerClass.InCSeq.of_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.LowerClass.InCSeq.of_all

/-- info: 'OrdinalAnalysis.Gentzen.Evaluate.eval_ev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Evaluate.eval_ev

/-! ### ω-completeness for true X-free sentences -/

/-- info: 'OrdinalAnalysis.Gentzen.OmegaTruth.omega_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.OmegaTruth.omega_complete

/-- info: 'OrdinalAnalysis.Gentzen.OmegaTruth.omega_complete_sentence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.OmegaTruth.omega_complete_sentence

/-! ### The evaluating instantiation, the replay, and general identity -/

-- Both of these lost `Classical.choice` when the infinitary calculus was
-- generalised over `OrdinalNotation`: the heights are now an abstract linearly
-- ordered type, so the classical content of mathlib's order on `NONote` is no
-- longer in the closure.  A *smaller* axiom set is still a pass.

/-- info: 'OrdinalAnalysis.OmegaDerivable.transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.OmegaDerivable.transport

/-- info: 'OrdinalAnalysis.OmegaDerivable.identity_general' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.OmegaDerivable.identity_general

/-- info: 'OrdinalAnalysis.Gentzen.Evaluate.ev_subst_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Evaluate.ev_subst_key

/-- info: 'OrdinalAnalysis.Gentzen.EvInst.omega_complete_sentence_ev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.EvInst.omega_complete_sentence_ev

/-- info: 'OrdinalAnalysis.Gentzen.NumSubst.numSubst_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.NumSubst.numSubst_free

/-- info: 'OrdinalAnalysis.Gentzen.Embed.replay_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Embed.replay_closed

/-! ### The evaluated class and the boundedness lemma -/

/-- info: 'OrdinalAnalysis.Gentzen.LowerClassEv.InCe.exhaustive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.LowerClassEv.InCe.exhaustive

/-- info: 'OrdinalAnalysis.Gentzen.Boundedness.boundedness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Boundedness.boundedness

/-- info: 'OrdinalAnalysis.Gentzen.Boundedness.not_derivable_TI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Boundedness.not_derivable_TI

/-! ### The induction axioms, derived in the evaluating calculus -/

/-- info: 'OrdinalAnalysis.Gentzen.AxiomsInduction.induction_axiom_derivable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.AxiomsInduction.induction_axiom_derivable

/-! ### The lower bound and Gentzen's theorem -/

/-- info: 'OrdinalAnalysis.Gentzen.AxiomsLogic.eq_axiom_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.AxiomsLogic.eq_axiom_derivable

/-- info: 'OrdinalAnalysis.Gentzen.AxiomsLogic.paMinus_axiom_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.AxiomsLogic.paMinus_axiom_derivable

/-- info: 'OrdinalAnalysis.Gentzen.LowerBound.gentzen_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.LowerBound.gentzen_lower_bound

/-- info: 'OrdinalAnalysis.Gentzen.gentzen_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.gentzen_theorem

/-- info: 'OrdinalAnalysis.Gentzen.paLX_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.paLX_consistent

/-! ### Veblen normal-form notations below Γ₀ -/

/-- info: 'OrdinalAnalysis.VNote.cmp_eq_cmp_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.VNote.cmp_eq_cmp_repr

/-- info: 'OrdinalAnalysis.VNote.repr_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.VNote.repr_inj

/-- info: 'OrdinalAnalysis.Gamma0Note.repr_veblenNote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.repr_veblenNote

/-! ### The natural sum on the Veblen notations; the coding is onto -/

/-- info: 'OrdinalAnalysis.Gamma0Note.nadd_lt_omegaPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.nadd_lt_omegaPow

/-- info: 'OrdinalAnalysis.Gamma0Note.ofNONote_lt_epsilonNote_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.ofNONote_lt_epsilonNote_zero

/-- info: 'OrdinalAnalysis.Gentzen.CodeSurj.isNF_surj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.CodeSurj.isNF_surj

/-! ### Second-order arithmetic: the ACA layer -/

/-- info: 'OrdinalAnalysis.ACA.rank_subst₂_lt_exs₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.rank_subst₂_lt_exs₂

/-- info: 'OrdinalAnalysis.ACA.soundness_ACA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.soundness_ACA

/-- info: 'OrdinalAnalysis.Gamma0Note.nadd_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.nadd_assoc

/-- info: 'OrdinalAnalysis.Gentzen.CodedVeblen.precN₁_code_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.CodedVeblen.precN₁_code_iff

/-- info: 'OrdinalAnalysis.Gentzen.VNoteBridge.isNF₁_surj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.VNoteBridge.isNF₁_surj

/-- info: 'OrdinalAnalysis.Gentzen.CodedVeblen.gamma0Order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.CodedVeblen.gamma0Order

/-- info: 'OrdinalAnalysis.OmegaDerivable.map_height' depends on axioms: [propext] -/
#guard_msgs in #print axioms OrdinalAnalysis.OmegaDerivable.map_height

/-- info: 'OrdinalAnalysis.Gentzen.Climb.ClimbData.climb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Climb.ClimbData.climb

/-- info: 'OrdinalAnalysis.Gentzen.ClimbEpsilon0.climb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.ClimbEpsilon0.climb

/-- info: 'OrdinalAnalysis.Gentzen.Epsilon1LowerBound.epsilon1_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Epsilon1LowerBound.epsilon1_lower_bound

/-- info: 'OrdinalAnalysis.Gentzen.Epsilon1LowerBound.paLX₁_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Epsilon1LowerBound.paLX₁_consistent

/-- info: 'OrdinalAnalysis.Gentzen.Epsilon1Axiom.TI₀_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Epsilon1Axiom.TI₀_derivable

/-- info: 'OrdinalAnalysis.Gentzen.ClimbVeblen.climb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.ClimbVeblen.climb

/-- info: 'OrdinalAnalysis.Gentzen.Epsilon1UpperBound.epsilon1_upper_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Epsilon1UpperBound.epsilon1_upper_bound

/-- info: 'OrdinalAnalysis.Gentzen.CodedVeblenJump.jumpA₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.CodedVeblenJump.jumpA₁

/-- info: 'OrdinalAnalysis.ACAOmega.OmegaDerivable₂.secondCutElimination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.OmegaDerivable₂.secondCutElimination

/-- info: 'OrdinalAnalysis.ACAOmega.OmegaDerivable₂.cutElimination_epsilon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.OmegaDerivable₂.cutElimination_epsilon

/-- info: 'OrdinalAnalysis.Gentzen.EpsilonSegmentOrder.not_derivable_TI_epsilon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.EpsilonSegmentOrder.not_derivable_TI_epsilon

/-- info: 'OrdinalAnalysis.OmegaDerivable.substX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.OmegaDerivable.substX

/-- info: 'OrdinalAnalysis.Gentzen.Epsilon1Scheme.scheme_axiom_derivable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Epsilon1Scheme.scheme_axiom_derivable

/-- info: 'OrdinalAnalysis.Gentzen.Epsilon1LowerBoundScheme.epsilon1_lower_bound_scheme' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Epsilon1LowerBoundScheme.epsilon1_lower_bound_scheme

/-- info: 'OrdinalAnalysis.Gentzen.Epsilon1LowerBoundScheme.paLX₁_scheme_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.Epsilon1LowerBoundScheme.paLX₁_scheme_consistent

/-- info: 'OrdinalAnalysis.Gentzen.epsilon1_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.epsilon1_theorem

/-- info: 'OrdinalAnalysis.Gentzen.paLX₁_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.paLX₁_consistent
