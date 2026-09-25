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

/-- info: 'OrdinalAnalysis.ACAOmega.evInst₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.evInst₂

/-- info: 'OrdinalAnalysis.ACAOmega.OmegaDerivable₂.evProvider' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.OmegaDerivable₂.evProvider

/-- info: 'OrdinalAnalysis.ACAOmega.OmegaDerivable₂.secondCutElimination_ev_Gamma0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.OmegaDerivable₂.secondCutElimination_ev_Gamma0

/-- info: 'OrdinalAnalysis.ACAOmega.OmegaDerivable₂.cutElimination_omegaAdd_ev' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.OmegaDerivable₂.cutElimination_omegaAdd_ev

/-- info: 'OrdinalAnalysis.Gentzen.VeblenEpsilon0UpperBound.concrete_eps0_ti' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.VeblenEpsilon0UpperBound.concrete_eps0_ti

/-- info: 'OrdinalAnalysis.Gentzen.VeblenTower.concrete_towerSucc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.VeblenTower.concrete_towerSucc

/-- info: 'OrdinalAnalysis.Gentzen.VeblenSuccStep.concrete_succ_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.VeblenSuccStep.concrete_succ_general

/-- info: 'OrdinalAnalysis.Gentzen.InternalEpsCover.concrete_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.InternalEpsCover.concrete_cover

/-- info: 'OrdinalAnalysis.Gentzen.InternalEpsMono.eps_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.InternalEpsMono.eps_mono

/-- info: 'OrdinalAnalysis.Gentzen.InternalEpsMonoCode.concrete_epsMono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.InternalEpsMonoCode.concrete_epsMono

/-- info: 'OrdinalAnalysis.ACAOmega.not_derivable_TI₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.not_derivable_TI₂

/-- info: 'OrdinalAnalysis.ACAOmega.not_derivable_TI₂_epsilonSeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.not_derivable_TI₂_epsilonSeg

/-- info: 'OrdinalAnalysis.ACAOmega.Embed₂.replay₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.Embed₂.replay₂

/-- info: 'OrdinalAnalysis.ACAOmega.Embed₂.replay₂_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.Embed₂.replay₂_closed

/-- info: 'OrdinalAnalysis.ACA.gen₂' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.gen₂

/-- info: 'OrdinalAnalysis.ACA.spec₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.spec₂

/-- info: 'OrdinalAnalysis.ACA.ACA_shift₁_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.ACA_shift₁_invariant

/-- info: 'OrdinalAnalysis.ACAOmega.Axioms₂.cut_axioms₂_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.Axioms₂.cut_axioms₂_of

/-- info: 'OrdinalAnalysis.ACAOmega.Axioms₂.aca_logical_axiom_derivable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.Axioms₂.aca_logical_axiom_derivable

/-- info: 'OrdinalAnalysis.ACAOmega.OmegaTruth₂.omega_complete₂_ev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.OmegaTruth₂.omega_complete₂_ev

/-- info: 'OrdinalAnalysis.ACAOmega.AxiomsInduction₂.succInd₂_derivable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.AxiomsInduction₂.succInd₂_derivable

/-- info: 'OrdinalAnalysis.NONote.repr_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.NONote.repr_succ

/-- info: 'OrdinalAnalysis.ACAOmega.OmegaDerivable₂.rank_le_omegaAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.OmegaDerivable₂.rank_le_omegaAdd

/-- info: 'OrdinalAnalysis.Gamma0Note.veblenStructure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.veblenStructure

/-- info: 'OrdinalAnalysis.ACAOmega.LowerBound₂.aca_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.LowerBound₂.aca_lower_bound

/-- info: 'OrdinalAnalysis.ACAOmega.LowerBound₂.aca_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.LowerBound₂.aca_consistent

/-- info: 'OrdinalAnalysis.ACAOmega.SchemeAxioms₂.aca_axiom_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.SchemeAxioms₂.aca_axiom_derivable

/-- info: 'OrdinalAnalysis.ACAOmega.ACATheorem.aca_lower_bound_statement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.ACATheorem.aca_lower_bound_statement

/-- info: 'OrdinalAnalysis.ACA.lift_paLX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.lift_paLX

/-- info: 'OrdinalAnalysis.ACA.allNums_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.allNums_mono

/-- info: 'OrdinalAnalysis.ACA.image_eqLX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.image_eqLX

/-- info: 'OrdinalAnalysis.ACAOmega.not_derivable_TI₂_gamma0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.not_derivable_TI₂_gamma0

/-- info: 'OrdinalAnalysis.Gamma0Note.closed_veblenNote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.closed_veblenNote

/-- info: 'OrdinalAnalysis.ACAOmega.OmegaDerivable₂.substX₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.OmegaDerivable₂.substX₂

/-- info: 'OrdinalAnalysis.ACAOmega.Climb₂.TIupto₂_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.Climb₂.TIupto₂_derivable

/-- info: 'OrdinalAnalysis.ACA.congruence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.congruence

/-- info: 'OrdinalAnalysis.ACA.image_indScheme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.image_indScheme

/-- info: 'OrdinalAnalysis.ACAOmega.Gamma0Theorem.gamma0_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.Gamma0Theorem.gamma0_theorem

/-- info: 'OrdinalAnalysis.ACAOmega.Gamma0Theorem.gamma0_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.Gamma0Theorem.gamma0_lower_bound

/-- info: 'OrdinalAnalysis.ACAOmega.Gamma0Theorem.acaΓ_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.Gamma0Theorem.acaΓ_consistent

/-- info: 'OrdinalAnalysis.ACAOmega.AxiomsTI₂.acaΓ_axiom_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.AxiomsTI₂.acaΓ_axiom_derivable

/-- info: 'OrdinalAnalysis.ACAOmega.Gamma0Segment.phi2_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACAOmega.Gamma0Segment.phi2_lower_bound

/-- info: 'OrdinalAnalysis.Gentzen.InternalVeblen.iveblen_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.InternalVeblen.iveblen_mono

/-- info: 'OrdinalAnalysis.Gentzen.InternalVeblen.iveblen_vmodelCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.InternalVeblen.iveblen_vmodelCode

/-- info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.reduction

/-- info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.secondCutEliminationR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.secondCutEliminationR

/-- info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.predicativeCutElimination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.predicativeCutElimination

/-- info: 'OrdinalAnalysis.Gentzen.InternalVebCover.veb_tower_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.InternalVebCover.veb_tower_cover

/-- info: 'OrdinalAnalysis.Gentzen.InternalVeblenCode.concrete_vebMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.InternalVeblenCode.concrete_vebMono

/-- info: 'OrdinalAnalysis.Gentzen.InternalVeblenCode.concrete_vebCover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.InternalVeblenCode.concrete_vebCover

/-- info: 'OrdinalAnalysis.ACA.towerInduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.towerInduction

/-- info: 'OrdinalAnalysis.ACA.aca_theorem_of_ti_epsilon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.aca_theorem_of_ti_epsilon

/-- info: 'OrdinalAnalysis.Ramified.replayR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.replayR

/-- info: 'OrdinalAnalysis.Ramified.evInstR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.evInstR

/-- info: 'OrdinalAnalysis.Gamma0Note.exists_lt_nadd_omegaPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.exists_lt_nadd_omegaPow

/--
info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.rankAbsorbed_powClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.rankAbsorbed_powClosed

/--
info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.predicativeCutStatement_powClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.predicativeCutStatement_powClosed

/--
info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.predicativeCut_veblen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.predicativeCut_veblen

/--
info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.cutElimination_veblen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.cutElimination_veblen

/-- info: 'OrdinalAnalysis.Ramified.naming_axiom_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.naming_axiom_derivable

/-- info: 'OrdinalAnalysis.Ramified.rank_evR_emb_naming_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.rank_evR_emb_naming_lt

/-- info: 'OrdinalAnalysis.Ramified.cut_axioms_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.cut_axioms_of

/-- info: 'OrdinalAnalysis.Ramified.rank_le_omegaPowLv_lvlOf_nadd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.rank_le_omegaPowLv_lvlOf_nadd

/-- info: 'OrdinalAnalysis.Gentzen.ProgStep.concrete_coverGood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.ProgStep.concrete_coverGood

/-- info: 'OrdinalAnalysis.Gentzen.ProgStep.concrete_progCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.ProgStep.concrete_progCover

/-- info: 'OrdinalAnalysis.Gentzen.ProgStep.concrete_succTI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.ProgStep.concrete_succTI

/-- info: 'OrdinalAnalysis.Gentzen.ProgStep.concrete_epsValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gentzen.ProgStep.concrete_epsValue

/-- info: 'OrdinalAnalysis.ACA.emb_psiE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.emb_psiE

/-- info: 'OrdinalAnalysis.ACA.lift_paLX_psi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.lift_paLX_psi

/-- info: 'OrdinalAnalysis.ACA.tiPsi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.tiPsi

/-- info: 'OrdinalAnalysis.ACA.succAllTI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.succAllTI

/-- info: 'OrdinalAnalysis.ACA.goodAllTI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.goodAllTI

/-- info: 'OrdinalAnalysis.ACA.epsProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.epsProg

/-- info: 'OrdinalAnalysis.ACA.ti_epsilon_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.ti_epsilon_all

/-- info: 'OrdinalAnalysis.ACA.aca_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.aca_upper_bound

/-- info: 'OrdinalAnalysis.ACA.aca_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.aca_theorem

/-- info: 'OrdinalAnalysis.Ramified.gamma0OrderR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.gamma0OrderR

/-- info: 'OrdinalAnalysis.Ramified.boundedness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.boundedness

/-- info: 'OrdinalAnalysis.Ramified.not_derivable_TI_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.not_derivable_TI_R

/-- info: 'OrdinalAnalysis.Ramified.not_derivable_TI_R_gamma0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.not_derivable_TI_R_gamma0

/-- info: 'OrdinalAnalysis.Ramified.eq_axiom_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.eq_axiom_derivable

/-- info: 'OrdinalAnalysis.Ramified.paMinus_axiom_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.paMinus_axiom_derivable

/-- info: 'OrdinalAnalysis.Ramified.induction_axiom_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.induction_axiom_derivable

/-- info: 'OrdinalAnalysis.Ramified.lvlOf_emb_lt_of_mem_RAlt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.lvlOf_emb_lt_of_mem_RAlt

/-- info: 'OrdinalAnalysis.Ramified.rank_evR_emb_lt_of_mem_RAlt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.rank_evR_emb_lt_of_mem_RAlt

/-- info: 'OrdinalAnalysis.Ramified.RAlt_axiom_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.RAlt_axiom_derivable

/-! ### Same-level parameters, comprehension, and cut elimination by blocks -/

/-- info: 'OrdinalAnalysis.Ramified.exists_jump_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.exists_jump_code

/-- info: 'OrdinalAnalysis.Ramified.exists_jump_code_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.exists_jump_code_lt

/-- info: 'OrdinalAnalysis.Ramified.exists_comprehension_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.exists_comprehension_code

/-- info: 'OrdinalAnalysis.Ramified.exists_naming' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.exists_naming

/-- info: 'OrdinalAnalysis.Ramified.exists_naming_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.exists_naming_lt

/-- info: 'OrdinalAnalysis.Ramified.rank_body_lt_memRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.rank_body_lt_memRank

/-- info: 'OrdinalAnalysis.Ramified.rank_lt_block_of_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.rank_lt_block_of_level

/-- info: 'OrdinalAnalysis.Ramified.rank_le_omegaMul_lvlOf_nadd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.rank_le_omegaMul_lvlOf_nadd

/-- info: 'OrdinalAnalysis.Ramified.guardTotal_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.guardTotal_provable

/-- info: 'OrdinalAnalysis.Ramified.RAlt_axiom_derivable'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.RAlt_axiom_derivable'

/-- info: 'OrdinalAnalysis.Ramified.RA_univ_axiom_derivable'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.RA_univ_axiom_derivable'

/-- info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.cutElimination_blocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.cutElimination_blocks

/-- info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.cutElimination_below_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.cutElimination_below_block

/-- info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.rank_inst_body_lt_rank_prAtom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.rank_inst_body_lt_rank_prAtom

/-! ### The non-provability half for the repaired ramified theories -/

/-- info: 'OrdinalAnalysis.Ramified.ramified_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.ramified_lower_bound

/-- info: 'OrdinalAnalysis.Ramified.ramified_lower_bound_veblen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.ramified_lower_bound_veblen

/-- info: 'OrdinalAnalysis.Ramified.provable_cutFree_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.provable_cutFree_of

/-- info: 'OrdinalAnalysis.Ramified.provable_cutFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.provable_cutFree

/-- info: 'OrdinalAnalysis.Ramified.provable_omegaDerivable_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.provable_omegaDerivable_of

/-- info: 'OrdinalAnalysis.Ramified.provable_omegaDerivable_chain_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.provable_omegaDerivable_chain_of

/-- info: 'OrdinalAnalysis.Ramified.provable_omegaDerivable_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.provable_omegaDerivable_univ

/-- info: 'OrdinalAnalysis.Ramified.RAlt_axiom_derivable_lt_epsilon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.RAlt_axiom_derivable_lt_epsilon

/-- info: 'OrdinalAnalysis.Ramified.naming_axiom_derivable_lt_epsilon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.naming_axiom_derivable_lt_epsilon

/-- info: 'OrdinalAnalysis.Ramified.vebSegOrderR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.vebSegOrderR

/-- info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.toBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.toBelow

/-- info: 'OrdinalAnalysis.ACA.jumpB_column_ACAplus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.jumpB_column_ACAplus

/-- info: 'OrdinalAnalysis.ACA.tiUpto_congr_column_ACAplus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.tiUpto_congr_column_ACAplus
/-- info: 'OrdinalAnalysis.Ramified.provable_omegaDerivable_chain_of_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.provable_omegaDerivable_chain_of_exists

/-- info: 'OrdinalAnalysis.Ramified.lift_paLX_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.lift_paLX_R

/-- info: 'OrdinalAnalysis.Ramified.provable_of_eqModels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.provable_of_eqModels

/-- info: 'OrdinalAnalysis.Ramified.tower_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.tower_provable

/-- info: 'OrdinalAnalysis.Ramified.epsProg_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.epsProg_provable

/-- info: 'OrdinalAnalysis.Ramified.tiPsi_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.tiPsi_provable

/-- info: 'OrdinalAnalysis.Ramified.descent_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.descent_provable

/-- info: 'OrdinalAnalysis.Ramified.vebSegOrderR_prec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.vebSegOrderR_prec_eq

/-- info: 'OrdinalAnalysis.Ramified.ramified_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.ramified_upper_bound

/-- info: 'OrdinalAnalysis.Ramified.ramified_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.ramified_theorem

/-- info: 'OrdinalAnalysis.ACA.ColumnTower.concrete_colTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.ColumnTower.concrete_colTower

/-- info: 'OrdinalAnalysis.ACA.columnTower_lifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.columnTower_lifted

/-- info: 'OrdinalAnalysis.ACA.omegaTowerInduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.omegaTowerInduction

/-- info: 'OrdinalAnalysis.ACA.ColumnTower.concrete_colProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.ColumnTower.concrete_colProg

/-- info: 'OrdinalAnalysis.ACA.ColumnTower.concrete_colEpsJump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.ColumnTower.concrete_colEpsJump

/-- info: 'OrdinalAnalysis.ACA.epsProg_plus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.epsProg_plus

/-- info: 'OrdinalAnalysis.ACA.colEpsJump_lifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.colEpsJump_lifted

/-- info: 'OrdinalAnalysis.ACA.tiExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.tiExt

/-- info: 'OrdinalAnalysis.ACA.epsJump_plus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.epsJump_plus

/-- info: 'OrdinalAnalysis.ACA.acaplus_tiUptoSeg_of_allTI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.acaplus_tiUptoSeg_of_allTI

/-- info: 'OrdinalAnalysis.ACA.allTI_epsIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.allTI_epsIter

/-- info: 'OrdinalAnalysis.ACA.exists_lt_epsIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.exists_lt_epsIter

/-- info: 'OrdinalAnalysis.ACA.aca_plus_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.aca_plus_upper_bound

/-- info: 'OrdinalAnalysis.ACA.aca_plus_upper_bound_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.aca_plus_upper_bound_seg

/-- info: 'OrdinalAnalysis.ACA.eval_omegaJumpAxiom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.eval_omegaJumpAxiom

/-- info: 'OrdinalAnalysis.ACA.soundness_ACAplus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.soundness_ACAplus

/-- info: 'OrdinalAnalysis.ACA.ACAplus_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.ACAplus_consistent

/-- info: 'OrdinalAnalysis.ACA.ACAplus₀_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ACA.ACAplus₀_consistent

/-- info: 'OrdinalAnalysis.Ramified.ramified_upper_bound_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.ramified_upper_bound_univ

/-- info: 'OrdinalAnalysis.Ramified.ramified_lower_bound_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.ramified_lower_bound_univ

/-- info: 'OrdinalAnalysis.Ramified.ramified_theorem_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.ramified_theorem_univ

/-- info: 'OrdinalAnalysis.Ramified.fs_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.fs_lower

/-! ### Notation levels: rank blocks, junk-empty literals, transfinite bounds -/

/-- info: 'OrdinalAnalysis.Gamma0Note.instEncodable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.instEncodable

/-- info: 'OrdinalAnalysis.VNote.nfb_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.VNote.nfb_iff

/-- info: 'OrdinalAnalysis.Gamma0Note.repr_omegaMulNote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.repr_omegaMulNote

/-- info: 'OrdinalAnalysis.Gamma0Note.repr_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.repr_blk

/-- info: 'OrdinalAnalysis.Gamma0Note.blkTop_le_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.blkTop_le_blk

/-- info: 'OrdinalAnalysis.Gamma0Note.blkTop_lt_blk_of_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.blkTop_lt_blk_of_limit

/-- info: 'OrdinalAnalysis.Ramified.rank_lt_blkTop_of_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.rank_lt_blkTop_of_level

/-- info: 'OrdinalAnalysis.Ramified.rank_lt_blk_of_level_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.rank_lt_blk_of_level_limit

/-- info: 'OrdinalAnalysis.Ramified.blk_ofNat_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.blk_ofNat_succ

/-- info: 'OrdinalAnalysis.Ramified.blkTop_ofNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.blkTop_ofNat

/-- info: 'OrdinalAnalysis.Ramified.rank_evR_emb_lt_blkTop_of_mem_RAlt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.rank_evR_emb_lt_blkTop_of_mem_RAlt

/-- info: 'OrdinalAnalysis.Ramified.cutRankR_lt_blkTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.cutRankR_lt_blkTop

/-- info: 'OrdinalAnalysis.Ramified.memFree_junkLitsR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.memFree_junkLitsR

/-- info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.mono_lits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.mono_lits

/-- info: 'OrdinalAnalysis.Ramified.boundedness_junk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.boundedness_junk

/-- info: 'OrdinalAnalysis.Ramified.not_derivable_TI_R_junk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.not_derivable_TI_R_junk

/-- info: 'OrdinalAnalysis.Ramified.not_derivable_TI_R_gamma0_junk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.not_derivable_TI_R_gamma0_junk

/-- info: 'OrdinalAnalysis.Ramified.fs_lower_junk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.fs_lower_junk

/-- info: 'OrdinalAnalysis.Ramified.provable_rank_height_of_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.provable_rank_height_of_exists

/-- info: 'OrdinalAnalysis.Ramified.cutFree_below_omegaPow_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.cutFree_below_omegaPow_succ

/-- info: 'OrdinalAnalysis.Ramified.blk_omegaPow_ofNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.blk_omegaPow_ofNat

/-- info: 'OrdinalAnalysis.Ramified.sf_lower_omegaPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.sf_lower_omegaPow

/-- info: 'OrdinalAnalysis.Ramified.ramified_lower_bound_omegaPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.ramified_lower_bound_omegaPow

/-- info: 'OrdinalAnalysis.Ramified.lt_omegaLv_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.lt_omegaLv_iff

/-- info: 'OrdinalAnalysis.Ramified.mem_RAlt_of_mem_RAlt_of_lvl_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.mem_RAlt_of_mem_RAlt_of_lvl_lt

/-- info: 'OrdinalAnalysis.Ramified.ramified_upper_bound_RA_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.ramified_upper_bound_RA_univ

/-- info: 'OrdinalAnalysis.Ramified.descent_code_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.descent_code_provable

/-- info: 'OrdinalAnalysis.Ramified.copy_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.copy_provable

/-- info: 'OrdinalAnalysis.Ramified.naming_param_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.naming_param_provable

/-- info: 'OrdinalAnalysis.Ramified.copy_naming_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.copy_naming_provable

/-- info: 'OrdinalAnalysis.Ramified.tiCopy_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.tiCopy_provable

/-- info: 'OrdinalAnalysis.Ramified.tiDown_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.tiDown_provable

/-- info: 'OrdinalAnalysis.Ramified.tiSucc_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.tiSucc_provable

/-- info: 'OrdinalAnalysis.Ramified.tiZero_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.tiZero_provable

/-- info: 'OrdinalAnalysis.Ramified.tiDown_code_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.tiDown_code_provable

/-- info: 'OrdinalAnalysis.Ramified.tiInst_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.tiInst_provable

/-- info: 'OrdinalAnalysis.Ramified.tiUptoSegR_downward_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.tiUptoSegR_downward_provable

/-- info: 'OrdinalAnalysis.Ramified.tiUptoSegR_downward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.tiUptoSegR_downward

/-- info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.invAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.invAll

/-- info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.cutR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.cutR

/-- info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.omegaRuleUniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.omegaRuleUniform

/-- info: 'OrdinalAnalysis.Ramified.OmegaDerivableR.weakening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.OmegaDerivableR.weakening

/-- info: 'OrdinalAnalysis.Ramified.uniformHeight_of_provable_all_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.uniformHeight_of_provable_all_of

/-- info: 'OrdinalAnalysis.Ramified.uniformHeight_of_provable_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.uniformHeight_of_provable_all

/-- info: 'OrdinalAnalysis.Ramified.sf_lower_omegaPow'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.sf_lower_omegaPow'

/-- info: 'OrdinalAnalysis.Ramified.ramified_lower_bound_omegaPow'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.ramified_lower_bound_omegaPow'

/-- info: 'OrdinalAnalysis.Gamma0Note.blk_omegaPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.blk_omegaPow

/--
info: 'OrdinalAnalysis.Gamma0Note.zero_or_exists_pred_or_isSuccLimit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.zero_or_exists_pred_or_isSuccLimit

/-- info: 'OrdinalAnalysis.Gamma0Note.succCover_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.succCover_zero

/-- info: 'OrdinalAnalysis.Gamma0Note.succCover_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.succCover_succ

/-- info: 'OrdinalAnalysis.Gamma0Note.limitCover_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.limitCover_zero

/-- info: 'OrdinalAnalysis.Gamma0Note.lt_lam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.lt_lam

/-- info: 'OrdinalAnalysis.Gamma0Note.veblenNote_lt_veblenNote_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.veblenNote_lt_veblenNote_iff

/-- info: 'OrdinalAnalysis.Gamma0Note.iterate_omegaPow_lt_epsilonNote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.iterate_omegaPow_lt_epsilonNote

/-- info: 'OrdinalAnalysis.Ramified.lvlOf_effBody_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.lvlOf_effBody_lt

/-- info: 'OrdinalAnalysis.Ramified.effBody_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.effBody_derivable

/-- info: 'OrdinalAnalysis.Ramified.effBody_iff_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.effBody_iff_derivable

/-- info: 'OrdinalAnalysis.Ramified.effBody_code_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.effBody_code_derivable

/-- info: 'OrdinalAnalysis.Ramified.rank_evR_effIff_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.rank_evR_effIff_lt

/-- info: 'OrdinalAnalysis.Ramified.good_code_effBodyAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.good_code_effBodyAt

/-- info: 'OrdinalAnalysis.Gamma0Note.fundSeq_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.fundSeq_lt

/-- info: 'OrdinalAnalysis.Gamma0Note.exists_lt_fundSeq_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.exists_lt_fundSeq_of_lt

/-- info: 'OrdinalAnalysis.Gamma0Note.iSup_repr_fundSeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.iSup_repr_fundSeq

/-- info: 'OrdinalAnalysis.Gamma0Note.succCover_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.succCover_limit

/-- info: 'OrdinalAnalysis.Gamma0Note.limitCover_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.limitCover_limit

/-- info: 'OrdinalAnalysis.Gamma0Note.limitCover_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Gamma0Note.limitCover_succ

/-- info: 'OrdinalAnalysis.lt_veblen_add_one_iff_of_isSuccLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.lt_veblen_add_one_iff_of_isSuccLimit

/-- info: 'OrdinalAnalysis.Ramified.descentBeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.descentBeta

/-- info: 'OrdinalAnalysis.Ramified.descentBeta_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.descentBeta_one

/-- info: 'OrdinalAnalysis.Ramified.descentAt_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.descentAt_all

/-- info: 'OrdinalAnalysis.Ramified.descent_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.descent_succ

/-- info: 'OrdinalAnalysis.Ramified.descent_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.descent_limit

/-- info: 'OrdinalAnalysis.Ramified.descent_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.descent_two

/-- info: 'OrdinalAnalysis.Ramified.hgtD_lt_epsilon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.hgtD_lt_epsilon

/-- info: 'OrdinalAnalysis.Ramified.hgtD_lt_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.hgtD_lt_of_fixed

/-- info: 'OrdinalAnalysis.Ramified.tiSeg_acc_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.tiSeg_acc_provable

/-- info: 'OrdinalAnalysis.Ramified.sf_stage0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.sf_stage0

/-- info: 'OrdinalAnalysis.Ramified.sf_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.sf_step

/-- info: 'OrdinalAnalysis.Ramified.aut_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.aut_all

/-- info: 'OrdinalAnalysis.Ramified.feferman_schutte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.feferman_schutte

/-- info: 'OrdinalAnalysis.Ramified.feferman_schutte_bound_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.feferman_schutte_bound_arith

/-- info: 'OrdinalAnalysis.Ramified.sf_lower_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.sf_lower_sharp

/-- info: 'OrdinalAnalysis.Ramified.sf_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.sf_upper

/-- info: 'OrdinalAnalysis.Ramified.sf_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.sf_theorem

/-- info: 'OrdinalAnalysis.Ramified.sf_theorem_epsilon_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.sf_theorem_epsilon_one

/-- info: 'OrdinalAnalysis.Ramified.sf_theorem_ofNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.sf_theorem_ofNat

/-- info: 'OrdinalAnalysis.Ramified.sf_theorem_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Ramified.sf_theorem_index

/-- info: 'OrdinalAnalysis.InductiveDef.ID1_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.ID1_consistent

/-- info: 'OrdinalAnalysis.InductiveDef.models_ID1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.models_ID1

/-- info: 'OrdinalAnalysis.InductiveDef.positive_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.positive_monotone

/-- info: 'OrdinalAnalysis.InductiveDef.ID1Acc_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.ID1Acc_consistent

/-- info: 'OrdinalAnalysis.InductiveDef.models_ID1Acc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.models_ID1Acc

/-- info: 'OrdinalAnalysis.InductiveDef.lfpA_accForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.lfpA_accForm

/-- info: 'OrdinalAnalysis.ThetaTerm.lt_trans'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaTerm.lt_trans'

/-- info: 'OrdinalAnalysis.ThetaTerm.lt_trichotomy'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaTerm.lt_trichotomy'

/-- info: 'OrdinalAnalysis.ThetaTerm.cmp_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaTerm.cmp_swap

/-- info: 'OrdinalAnalysis.ThetaNote.linearOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.linearOrder

/-- info: 'OrdinalAnalysis.ThetaTerm.theta_lt_theta_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaTerm.theta_lt_theta_iff

/-- info: 'OrdinalAnalysis.ThetaTerm.forall_E_lt_theta_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaTerm.forall_E_lt_theta_iff

/-- info: 'OrdinalAnalysis.ThetaTerm.exists_mem_E_le_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaTerm.exists_mem_E_le_of_le

/-- info: 'OrdinalAnalysis.ThetaNote.nadd_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.nadd_comm

/-- info: 'OrdinalAnalysis.ThetaNote.nadd_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.nadd_assoc

/-- info: 'OrdinalAnalysis.ThetaNote.nadd_lt_nadd_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.nadd_lt_nadd_left

/-- info: 'OrdinalAnalysis.ThetaNote.omegaPow_lt_omegaPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.omegaPow_lt_omegaPow

/-- info: 'OrdinalAnalysis.ThetaNote.nadd_lt_omegaPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.nadd_lt_omegaPow

/-- info: 'OrdinalAnalysis.ThetaNote.add_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.add_assoc

/-- info: 'OrdinalAnalysis.ThetaNote.omegaPow_eq_self_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.omegaPow_eq_self_iff

/-- info: 'OrdinalAnalysis.ThetaNote.ordinalNotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.ordinalNotation

/-- info: 'OrdinalAnalysis.ThetaNote.wellFoundedLT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.wellFoundedLT

/-- info: 'OrdinalAnalysis.ThetaNote.instOrdinalNotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.instOrdinalNotation

/-- info: 'OrdinalAnalysis.ThetaTerm.isAcc_theta_of_dist_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaTerm.isAcc_theta_of_dist_of_forall

/-- info: 'OrdinalAnalysis.ThetaTerm.isAcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaTerm.isAcc

/-- info: 'OrdinalAnalysis.ThetaNote.bhOrdinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.bhOrdinal

/-- info: 'OrdinalAnalysis.ThetaNote.theta_isLeast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.theta_isLeast

/-- info: 'OrdinalAnalysis.ThetaNote.lt_theta_of_mem_Cset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.lt_theta_of_mem_Cset

/-- info: 'OrdinalAnalysis.ThetaNote.Hop_nice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.Hop_nice

/-- info: 'OrdinalAnalysis.ThetaNote.theta_lt_theta_of_mem_Hop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.theta_lt_theta_of_mem_Hop

/-- info: 'OrdinalAnalysis.ThetaNote.theta_mem_Hop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.theta_mem_Hop

/-- info: 'OrdinalAnalysis.ThetaNote.exists_lt_theta_omegaTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaNote.exists_lt_theta_omegaTower

/-- info: 'OrdinalAnalysis.InductiveDef.rk_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.rk_neg

/-- info: 'OrdinalAnalysis.InductiveDef.rk_subst_lt_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.rk_subst_lt_all

/-- info: 'OrdinalAnalysis.InductiveDef.rk_IOmegaAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.rk_IOmegaAt

/-- info: 'OrdinalAnalysis.InductiveDef.rk_unfold_lt_stageAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.rk_unfold_lt_stageAt

/-- info: 'OrdinalAnalysis.InductiveDef.sigmaOmega_rk_le_Omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.sigmaOmega_rk_le_Omega

/-- info: 'OrdinalAnalysis.InductiveDef.rk_lt_Omega_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.rk_lt_Omega_iff

/-- info: 'OrdinalAnalysis.InductiveDef.sigmaOmega_embed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.sigmaOmega_embed_iff

/-- info: 'OrdinalAnalysis.InductiveDef.cap_unfold_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.cap_unfold_top

/-- info: 'OrdinalAnalysis.ID1.Internal.decode_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.decode_code

/-- info: 'OrdinalAnalysis.ID1.Internal.iltb_mc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.iltb_mc

/-- info: 'OrdinalAnalysis.ID1.Internal.isNF_mc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.isNF_mc

/-- info: 'OrdinalAnalysis.ID1.Internal.precN_codeNote_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.precN_codeNote_iff

/-- info: 'OrdinalAnalysis.ID1.Internal.precFieldN_exists_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.precFieldN_exists_lt

/-- info: 'OrdinalAnalysis.ID1.Internal.thetaOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.thetaOrder

/-- info: 'OrdinalAnalysis.ID1.Internal.thetaFieldOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.thetaFieldOrder

/-- info: 'OrdinalAnalysis.ID1.Internal.eval_thLtDef_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.eval_thLtDef_code

/-- info: 'OrdinalAnalysis.InductiveDef.IDerivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.IDerivable

/-- info: 'OrdinalAnalysis.InductiveDef.IDerivable.weaken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.IDerivable.weaken

/-- info: 'OrdinalAnalysis.InductiveDef.IDerivable.inv_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.IDerivable.inv_all

/-- info: 'OrdinalAnalysis.InductiveDef.boundedness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.boundedness

/-- info: 'OrdinalAnalysis.InductiveDef.neg_stage_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.neg_stage_bound

/-- info: 'OrdinalAnalysis.InductiveDef.collapsing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.collapsing

/-- info: 'OrdinalAnalysis.InductiveDef.collapsing_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.collapsing_zero

/-- info: 'OrdinalAnalysis.InductiveDef.IDerivable.reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.IDerivable.reduction

/-- info: 'OrdinalAnalysis.InductiveDef.IDerivable.reduction_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.IDerivable.reduction_cut

/-- info: 'OrdinalAnalysis.InductiveDef.IDerivable.elimination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.IDerivable.elimination

/-- info: 'OrdinalAnalysis.InductiveDef.IDerivable.elimination_iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.IDerivable.elimination_iter

/-- info: 'OrdinalAnalysis.InductiveDef.collapsing_embedded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.collapsing_embedded

/-- info: 'OrdinalAnalysis.InductiveDef.theta_omegaTower_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.theta_omegaTower_lt

/-- info: 'OrdinalAnalysis.InductiveDef.corollary_7_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.corollary_7_2

/-- info: 'OrdinalAnalysis.ID1.Internal.iltb_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.iltb_trans

/-- info: 'OrdinalAnalysis.ID1.Internal.iltb_trichotomy_nf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.iltb_trichotomy_nf

/-- info: 'OrdinalAnalysis.ID1.Internal.forall_iinE_lt_theta_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.forall_iinE_lt_theta_iff

/-- info: 'OrdinalAnalysis.ID1.Internal.exists_iinE_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.exists_iinE_le_of_le

/-- info: 'OrdinalAnalysis.ID1.Internal.iadd_mc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.iadd_mc

/-- info: 'OrdinalAnalysis.ID1.Internal.inadd_mc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.inadd_mc

/-- info: 'OrdinalAnalysis.ID1.Internal.iomegaPow_mc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.iomegaPow_mc

/-- info: 'OrdinalAnalysis.ID1.Internal.iadd_lt_iomegaPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.iadd_lt_iomegaPow

/-- info: 'OrdinalAnalysis.ID1.Internal.iomegaPow_lt_prin_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.iomegaPow_lt_prin_iff

/-- info: 'OrdinalAnalysis.ID1.Internal.iadd_iomegaPow_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ID1.Internal.iadd_iomegaPow_tail

/-- info: 'OrdinalAnalysis.InductiveDef.StageSem.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.StageSem.sound

/--
info: 'OrdinalAnalysis.InductiveDef.StageSem.codeNote_mem_stageSet_acc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.StageSem.codeNote_mem_stageSet_acc

/--
info: 'OrdinalAnalysis.InductiveDef.LowerBound.provable_fieldInI_of_ti' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.LowerBound.provable_fieldInI_of_ti

/--
info: 'OrdinalAnalysis.InductiveDef.LowerBound.not_derivable_fieldInI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.LowerBound.not_derivable_fieldInI

/--
info: 'OrdinalAnalysis.InductiveDef.LowerBound.id1_lower_bound_of_embedding_xfree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.LowerBound.id1_lower_bound_of_embedding_xfree

/--
info: 'OrdinalAnalysis.InductiveDef.LowerBound.id1_lower_bound_of_embedding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.LowerBound.id1_lower_bound_of_embedding

/-- info: 'OrdinalAnalysis.InductiveDef.taut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.taut

/-- info: 'OrdinalAnalysis.InductiveDef.closure_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.closure_derivable

/-- info: 'OrdinalAnalysis.InductiveDef.indAx_axiom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.indAx_axiom

/-- info: 'OrdinalAnalysis.InductiveDef.ax_derivable_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.ax_derivable_of_mem

/-- info: 'OrdinalAnalysis.InductiveDef.embedding_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.embedding_theorem

/-- info: 'OrdinalAnalysis.InductiveDef.embedding_theorem_xfree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.embedding_theorem_xfree

/-- info: 'OrdinalAnalysis.InductiveDef.embedding_theorem_Hop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.embedding_theorem_Hop

/-- info: 'OrdinalAnalysis.InductiveDef.id1_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.id1_lower_bound

/-- info: 'OrdinalAnalysis.InductiveDef.embedding_accForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.embedding_accForm

/-- info: 'OrdinalAnalysis.InductiveDef.id1_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.id1_theorem

/-- info: 'OrdinalAnalysis.InductiveDef.UpperBound.id1_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.UpperBound.id1_upper_bound

/-- info: 'OrdinalAnalysis.InductiveDef.Lift.provable_of_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.Lift.provable_of_models

/--
info: 'OrdinalAnalysis.InductiveDef.UpperBound.tiUptoSentence_Omega' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.UpperBound.tiUptoSentence_Omega

/-- info: 'OrdinalAnalysis.InductiveDef.id1_theorem'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.InductiveDef.id1_theorem'

/-- info: 'OrdinalAnalysis.ThetaW2Note.wellFoundedLT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaW2Note.wellFoundedLT

/-- info: 'OrdinalAnalysis.ThetaWNote.not_wellFoundedLT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNote.not_wellFoundedLT

/-- info: 'OrdinalAnalysis.ThetaWTerm.not_dom_tower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWTerm.not_dom_tower

/-- info: 'OrdinalAnalysis.ThetaWTerm.lt_theta0_Omega_of_levLT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWTerm.lt_theta0_Omega_of_levLT

/-- info: 'OrdinalAnalysis.ThetaWNoteD.wellFoundedLT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.wellFoundedLT

/-- info: 'OrdinalAnalysis.ThetaWNoteD.dom_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.dom_add

/-- info: 'OrdinalAnalysis.ThetaWNoteD.dom_phi_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.dom_phi_of_lt

/-- info: 'OrdinalAnalysis.IDn.models_ID' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.models_ID

/-- info: 'OrdinalAnalysis.IDn.IDn_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.IDn_consistent

/-- info: 'OrdinalAnalysis.IDn.IDlt_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.IDlt_consistent

/-- info: 'OrdinalAnalysis.IDn.provable_IDlt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.provable_IDlt_iff

/-- info: 'OrdinalAnalysis.IDn.rk_lt_Omega_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.rk_lt_Omega_iff

/-- info: 'OrdinalAnalysis.IDn.rk_unfold_lt_stageAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.rk_unfold_lt_stageAt

/-- info: 'OrdinalAnalysis.IDn.sigmaW_embed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.sigmaW_embed_iff

/-- info: 'OrdinalAnalysis.IDn.Internal.isTerm_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Internal.isTerm_iff

/-- info: 'OrdinalAnalysis.IDn.Internal.iinE_mc_mc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Internal.iinE_mc_mc

/-- info: 'OrdinalAnalysis.IDn.Internal.iinG_mc_mc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Internal.iinG_mc_mc

/-- info: 'OrdinalAnalysis.ThetaWNoteD.theta_isLeast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.theta_isLeast

/-- info: 'OrdinalAnalysis.ThetaWNoteD.dom_lt_theta0_omegaTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.dom_lt_theta0_omegaTower

/-- info: 'OrdinalAnalysis.ThetaWNoteD.dom_exists_lt_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.dom_exists_lt_c

/-- info: 'OrdinalAnalysis.ThetaWNoteD.theta_isLeastS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.theta_isLeastS

/-- info: 'OrdinalAnalysis.ThetaWNoteD.dom_add_omegaPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.dom_add_omegaPow

/-- info: 'OrdinalAnalysis.ThetaWNoteD.not_dom_add_omegaPow_Hop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.not_dom_add_omegaPow_Hop

/-- info: 'OrdinalAnalysis.Notn.thetaWCN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Notn.thetaWCN

/-- info: 'OrdinalAnalysis.Notn.thetaWLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Notn.thetaWLevel

/-- info: 'OrdinalAnalysis.Notn.thetaWTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.Notn.thetaWTower

/-- info: 'OrdinalAnalysis.IDn.Internal.iltb_mc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Internal.iltb_mc

/-- info: 'OrdinalAnalysis.IDn.Internal.isDom_mc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Internal.isDom_mc

/-- info: 'OrdinalAnalysis.IDn.Internal.standard_dom_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Internal.standard_dom_iff

/-- info: 'OrdinalAnalysis.IDn.smoke_I1_omega2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.smoke_I1_omega2

/-- info: 'OrdinalAnalysis.IDn.smoke_I1_stage_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.smoke_I1_stage_zero

/-- info: 'OrdinalAnalysis.IDn.IDnDerivable.reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.IDnDerivable.reduction

/-- info: 'OrdinalAnalysis.IDn.IDnDerivable.reduction_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.IDnDerivable.reduction_cut

/-- info: 'OrdinalAnalysis.IDn.Collapsing.psi_hat_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Collapsing.psi_hat_mem

/-- info: 'OrdinalAnalysis.IDn.Collapsing.drop_stage_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Collapsing.drop_stage_zero

/-- info: 'OrdinalAnalysis.IDn.boundedness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.boundedness

/-- info: 'OrdinalAnalysis.IDn.neg_stage_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.neg_stage_bound

/-- info: 'OrdinalAnalysis.ThetaWNoteD.phi_lt_phi_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.phi_lt_phi_right

/-- info: 'OrdinalAnalysis.ThetaWNoteD.lt_phi_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.lt_phi_of_lt

/-- info: 'OrdinalAnalysis.IDn.Internal.iltb_trichotomy_nf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Internal.iltb_trichotomy_nf

/-- info: 'OrdinalAnalysis.IDn.Internal.iltb_expList_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Internal.iltb_expList_iff

/-- info: 'OrdinalAnalysis.IDn.IDnDerivable.elimination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.IDnDerivable.elimination

/-- info: 'OrdinalAnalysis.IDn.IDnDerivable.elimination_iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.IDnDerivable.elimination_iter

/-- info: 'OrdinalAnalysis.ThetaWNoteD.phi_lt_phi_of_lt_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.phi_lt_phi_of_lt_left

/-- info: 'OrdinalAnalysis.ThetaWNoteD.lt_phi_right_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.lt_phi_right_self

/-- info: 'OrdinalAnalysis.ThetaWNoteD.succ_le_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.succ_le_of_lt

/-- info: 'OrdinalAnalysis.IDn.Collapsing.collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Collapsing.collapse

/-- info: 'OrdinalAnalysis.IDn.Collapsing.collapse_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Collapsing.collapse_zero

/-- info: 'OrdinalAnalysis.IDn.Collapsing.collapse_zero_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Collapsing.collapse_zero_bound

/-- info: 'OrdinalAnalysis.IDn.Collapsing.collapse_case_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Collapsing.collapse_case_cut

/-- info: 'OrdinalAnalysis.IDn.Collapsing.collapse_case_fix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Collapsing.collapse_case_fix

/-- info: 'OrdinalAnalysis.IDn.Upper.idn_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Upper.idn_upper_bound

/-- info: 'OrdinalAnalysis.IDn.Upper.idlt_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Upper.idlt_upper_bound

/-- info: 'OrdinalAnalysis.IDn.Upper.idlt_upper_bound_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Upper.idlt_upper_bound_finite

/-- info: 'OrdinalAnalysis.IDn.StageSem.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.StageSem.sound

/-- info: 'OrdinalAnalysis.IDn.StageSem.eval_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.StageSem.eval_unfold

/-- info: 'OrdinalAnalysis.ThetaWNoteD.phiClosed_HopS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.phiClosed_HopS

/-- info: 'OrdinalAnalysis.IDn.noOmega_muBar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.noOmega_muBar

/-- info: 'OrdinalAnalysis.IDn.Internal.codedOrderFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Internal.codedOrderFacts

/-- info: 'OrdinalAnalysis.IDn.Upper.idn_upper_bound'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Upper.idn_upper_bound'

/-- info: 'OrdinalAnalysis.IDn.Upper.idlt_upper_bound'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Upper.idlt_upper_bound'

/-- info: 'OrdinalAnalysis.IDn.predicative_cut_elim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.predicative_cut_elim

/-- info: 'OrdinalAnalysis.IDn.collapseHyps_predCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.collapseHyps_predCut

/-- info: 'OrdinalAnalysis.IDn.collapseHyps_of_levelBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.collapseHyps_of_levelBounded

/-- info: 'OrdinalAnalysis.IDn.embedding_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.embedding_theorem

/-- info: 'OrdinalAnalysis.IDn.embedding_theorem_xfree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.embedding_theorem_xfree

/-- info: 'OrdinalAnalysis.IDn.noXN_rew' depends on axioms: [propext] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.noXN_rew

/-- info: 'OrdinalAnalysis.IDn.lMap_swapN_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.lMap_swapN_rel

/-- info: 'OrdinalAnalysis.IDn.Upper.wFormsOmega_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Upper.wFormsOmega_positive

/-- info: 'OrdinalAnalysis.IDn.Upper.wFormsOmega_levelBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Upper.wFormsOmega_levelBounded

/-- info: 'OrdinalAnalysis.IDn.Internal.eval_lt_iff_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Internal.eval_lt_iff_lt

/-- info: 'OrdinalAnalysis.IDn.Internal.eval_fld_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Internal.eval_fld_iff

/-- info: 'OrdinalAnalysis.IDn.Internal.fld_surj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.Internal.fld_surj

/-- info: 'OrdinalAnalysis.IDn.IDnDerivable.replace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.IDnDerivable.replace

/-- info: 'OrdinalAnalysis.IDn.numI_freeVariables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.numI_freeVariables

/-- info: 'OrdinalAnalysis.IDn.provable_fieldInI0_of_ti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.provable_fieldInI0_of_ti

/-- info: 'OrdinalAnalysis.IDn.codeAt0_mem_stageSetN_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.codeAt0_mem_stageSetN_iff

/-- info: 'OrdinalAnalysis.IDn.eq_axiom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.eq_axiom

/-- info: 'OrdinalAnalysis.IDn.paMinus_axiom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.paMinus_axiom

/-- info: 'OrdinalAnalysis.IDn.induction_axiom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.induction_axiom

/-- info: 'OrdinalAnalysis.IDn.embedHyps_induction_of_pa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.embedHyps_induction_of_pa

/-- info: 'OrdinalAnalysis.IDn.OmegaTwo_pa_le_OmegaTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.OmegaTwo_pa_le_OmegaTwo

/-- info: 'OrdinalAnalysis.IDn.embedHypsLogicPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.embedHypsLogicPart

/-- info: 'OrdinalAnalysis.ThetaWNoteD.add_eq_nadd_of_forall_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.add_eq_nadd_of_forall_le

/-- info: 'OrdinalAnalysis.IDn.idn_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.idn_lower_bound

/-- info: 'OrdinalAnalysis.IDn.idn_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.idn_theorem

/-- info: 'OrdinalAnalysis.IDn.idlt_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.idlt_theorem

/-- info: 'OrdinalAnalysis.IDn.plugI_lMap_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.plugI_lMap_top

/-- info: 'OrdinalAnalysis.IDn.embK_substI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.embK_substI

/-- info: 'OrdinalAnalysis.IDn.collapseCorollary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.collapseCorollary

/-- info: 'OrdinalAnalysis.IDn.idn_lower_bound'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.idn_lower_bound'

/-- info: 'OrdinalAnalysis.IDn.embedHyps_replaceHeadNumI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.embedHyps_replaceHeadNumI

/-- info: 'OrdinalAnalysis.ThetaWNoteD.theta0_hat_lt_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.ThetaWNoteD.theta0_hat_lt_c

/-- info: 'OrdinalAnalysis.IDn.psi0_hat_lt_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.psi0_hat_lt_c

/-- info: 'OrdinalAnalysis.IDn.idn_theorem_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.idn_theorem_sharp

/-- info: 'OrdinalAnalysis.IDn.ex63' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.ex63

/-- info: 'OrdinalAnalysis.IDn.plugI_subst_numI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.plugI_subst_numI

/-- info: 'OrdinalAnalysis.IDn.taut_additive_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.taut_additive_impossible

/-- info: 'OrdinalAnalysis.IDn.collapseCorollarySharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.collapseCorollarySharp

/-- info: 'OrdinalAnalysis.IDn.idn_theorem_sharp'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.idn_theorem_sharp'

/-- info: 'OrdinalAnalysis.IDn.idn_lower_bound_sharp'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.idn_lower_bound_sharp'

/-- info: 'OrdinalAnalysis.IDn.embedHyps_taut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.embedHyps_taut

/-- info: 'OrdinalAnalysis.IDn.closure_axiom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.closure_axiom

/-- info: 'OrdinalAnalysis.IDn.indAx_axiom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.indAx_axiom

/-- info: 'OrdinalAnalysis.IDn.embedHyps_wForms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.embedHyps_wForms

/-- info: 'OrdinalAnalysis.IDn.idn_theorem_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.idn_theorem_final

/-- info: 'OrdinalAnalysis.IDn.idn_analysis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.idn_analysis

/-- info: 'OrdinalAnalysis.IDn.idn_lower_bound_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.idn_lower_bound_unconditional

/-- info: 'OrdinalAnalysis.IDn.wForms_indAx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.wForms_indAx

/-- info: 'OrdinalAnalysis.IDn.idseq_to_idn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.idseq_to_idn

/-- info: 'OrdinalAnalysis.IDn.idlt_analysis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OrdinalAnalysis.IDn.idlt_analysis
