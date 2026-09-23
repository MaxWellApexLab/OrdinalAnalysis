/-
  The capstone `lift_paLX`.

  `translate` (`Translate.lean`) turns a `paLX`-derivation into an
  `ACA`-derivation of the `toSOAt`-images, with the *images of the axioms used*
  still sitting in the context as hypotheses.  `Toolkit.lean`'s `cutMany` cuts
  them away, provided each is separately `Provable ACA`.  So the whole of
  `lift_paLX` reduces to one statement — `lift_of_axiomImages` below — plus a
  case analysis of `paLX = 𝗘𝗤 LX ∪ (Theory.lMap toLX 𝗣𝗔⁻ ∪ InductionScheme LX Set.univ)`:

  * `Theory.lMap toLX 𝗣𝗔⁻` — the image is the `lift` of the `ℒₒᵣ`-axiom
    (`toSOAtB_lMap`), i.e. a member of `paMinus ⊆ ACA₀`;
  * `𝗘𝗤 LX` — `refl`/`symm`/`trans`/`funcExt (Sum.inl f)`/`relExt (Sum.inl r)`
    are `lMap`-images of the corresponding `ℒₒᵣ`-axioms, hence members of
    `eqAxioms ⊆ ACA₀`; `funcExt (Sum.inr e)` is vacuous (`XLang` has no function
    symbols); `relExt (Sum.inr XRel.X)` is the one genuinely second-order case —
    the *congruence* statement for `ψ`, which is `CongruenceStatement ψ` below;
  * `InductionScheme LX Set.univ` — the image is an instance of `ACA`'s own
    induction scheme, recovered from the closed axiom `indScheme₂` by
    `Toolkit.lean`'s `specSets` and `Translate.lean`'s `subst₁_toSOAtB`.  This is
    the whole point of `toSOAtB`'s bound-set-slot count.
-/
import OrdinalAnalysis.ACA.Combinators
import OrdinalAnalysis.ACA.Congruence
import OrdinalAnalysis.ACA.LiftInduction
import OrdinalAnalysis.ACA.Translate

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX XRel Xat toLX paLX)

/-! ### The reduction to the axiom images -/

/-- **`lift_paLX`, modulo the images of the axioms.**  `provable_iff` →
`translate` → `cutMany`.  Nothing here is specific to `paLX`. -/
theorem lift_of_axiomImages (ψ : Semiformula ℒₒᵣ ℕ Empty 0 1)
    (himg : ∀ σ ∈ paLX, Provable ACA (toSOAt ψ (FirstOrder.Rewriting.emb σ)))
    {σ : FirstOrder.Sentence LX} (h : paLX ⊢ σ) :
    Provable ACA (toSOAt ψ (FirstOrder.Rewriting.emb σ)) := by
  obtain ⟨Γ, hΓ, ⟨d⟩⟩ := FirstOrder.Theory.Proof.provable_iff.mp h
  have d' := translate ψ d
  have hneg : ∀ L : List (FirstOrder.Semiformula LX ℕ 0),
      List.map (toSOAt ψ) (List.map (fun x => ∼x) L) =
        List.map (fun x : Proposition ℒₒᵣ => ∼x) (List.map (toSOAt ψ) L) := by
    intro L
    simp only [List.map_map, Function.comp_def, toSOAtB_neg]
  have hmap : ((FirstOrder.Rewriting.emb σ ::
        ∼(FirstOrder.Sequent.embed Γ)).map (toSOAt ψ)) =
      toSOAt ψ (FirstOrder.Rewriting.emb σ) ::
        ∼((FirstOrder.Sequent.embed Γ).map (toSOAt ψ)) := by
    show toSOAt ψ (FirstOrder.Rewriting.emb σ) ::
      List.map (toSOAt ψ) (List.map (fun x => ∼x) (FirstOrder.Sequent.embed Γ)) = _
    rw [hneg]
    rfl
  refine cutMany (Δ := (FirstOrder.Sequent.embed Γ).map (toSOAt ψ)) ?_
    (Derivation.cast d' hmap)
  intro χ hχ
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hχ
  obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hρ
  exact himg τ (hΓ τ hτ)

/-! ### The image of the arithmetical axioms

`toSOAtB_lMap` says the image of a formula transported from `ℒₒᵣ` is its
`lift`, whatever `ψ` is.  Both `Theory.lMap toLX 𝗣𝗔⁻` and the `Sum.inl` part of
`𝗘𝗤 LX` are of that shape. -/

/-- The image of a transported `ℒₒᵣ`-sentence is its `liftSentence`. -/
theorem toSOAt_lMap_sentence {ψ : Semiformula ℒₒᵣ ℕ Empty 0 1}
    (σ : FirstOrder.Sentence ℒₒᵣ) :
    toSOAt ψ (FirstOrder.Rewriting.emb (FirstOrder.Semiformula.lMap toLX σ)) =
      liftSentence σ := by
  rw [show (FirstOrder.Rewriting.emb (FirstOrder.Semiformula.lMap toLX σ) :
        FirstOrder.Semiformula LX ℕ 0) =
      FirstOrder.Semiformula.lMap toLX (FirstOrder.Rewriting.emb σ) from by
    simp [FirstOrder.Semiformula.lMap_emb]]
  exact toSOAtB_lMap _

/-- **The image of `Theory.lMap toLX 𝗣𝗔⁻`.** -/
theorem image_paMinus (ψ : Semiformula ℒₒᵣ ℕ Empty 0 1) {σ : FirstOrder.Sentence LX}
    (h : σ ∈ FirstOrder.Theory.lMap toLX 𝗣𝗔⁻) :
    Provable ACA (toSOAt ψ (FirstOrder.Rewriting.emb σ)) := by
  obtain ⟨σ₀, hσ₀, rfl⟩ := h
  rw [toSOAt_lMap_sentence σ₀]
  exact provable_mono ACA₀_subset_ACA
    (ofAxiom (paMinus_subset_ACA₀ ⟨σ₀, hσ₀, rfl⟩))

/-! ### The image of the equality axioms

The `Sum.inl` part of `𝗘𝗤 LX` is literally the `lMap`-image of `𝗘𝗤 ℒₒᵣ`: the
`Language.ORing LX` instance sends every arithmetical symbol to its `Sum.inl`
tag, which is exactly what `toLX` does. -/

/-- The defining sentence of the equality operator is transported by `toLX`. -/
private theorem toLX_rel {k : ℕ} (r : (ℒₒᵣ).Rel k) : toLX.rel r = Sum.inl r := rfl

private theorem toLX_func {k : ℕ} (f : (ℒₒᵣ).Func k) : toLX.func f = Sum.inl f := rfl

private theorem lMap_eqSentence :
    FirstOrder.Semiformula.lMap toLX
        (FirstOrder.Semiformula.Operator.Eq.eq (L := ℒₒᵣ)).sentence =
      (FirstOrder.Semiformula.Operator.Eq.eq (L := LX)).sentence := rfl

theorem lMap_eq_refl :
    FirstOrder.Theory.Eq.refl LX =
      FirstOrder.Semiformula.lMap toLX (FirstOrder.Theory.Eq.refl ℒₒᵣ) := by
  simp [FirstOrder.Theory.Eq.refl, FirstOrder.Semiformula.Operator.operator,
    FirstOrder.Semiformula.lMap_subst, FirstOrder.Semiformula.lMap_emb, ← lMap_eqSentence]

theorem lMap_eq_symm :
    FirstOrder.Theory.Eq.symm LX =
      FirstOrder.Semiformula.lMap toLX (FirstOrder.Theory.Eq.symm ℒₒᵣ) := by
  simp [FirstOrder.Theory.Eq.symm, FirstOrder.Semiformula.Operator.operator,
    FirstOrder.Semiformula.lMap_subst, FirstOrder.Semiformula.lMap_emb, ← lMap_eqSentence]

theorem lMap_eq_trans :
    FirstOrder.Theory.Eq.trans LX =
      FirstOrder.Semiformula.lMap toLX (FirstOrder.Theory.Eq.trans ℒₒᵣ) := by
  simp [FirstOrder.Theory.Eq.trans, FirstOrder.Semiformula.Operator.operator,
    FirstOrder.Semiformula.lMap_subst, FirstOrder.Semiformula.lMap_emb, ← lMap_eqSentence]

theorem lMap_eq_funcExt {k : ℕ} (f : (ℒₒᵣ).Func k) :
    FirstOrder.Theory.Eq.funcExt (L := LX) (Sum.inl f) =
      FirstOrder.Semiformula.lMap toLX (FirstOrder.Theory.Eq.funcExt f) := by
  simp [FirstOrder.Theory.Eq.funcExt, FirstOrder.Semiformula.Operator.operator,
    FirstOrder.Semiformula.lMap_subst, FirstOrder.Semiformula.lMap_emb, ← lMap_eqSentence,
    Function.comp_def, Matrix.comp_vecCons', Matrix.constant_eq_singleton, toLX_rel,
    toLX_func]

theorem lMap_eq_relExt {k : ℕ} (r : (ℒₒᵣ).Rel k) :
    FirstOrder.Theory.Eq.relExt (L := LX) (Sum.inl r) =
      FirstOrder.Semiformula.lMap toLX (FirstOrder.Theory.Eq.relExt r) := by
  simp [FirstOrder.Theory.Eq.relExt, FirstOrder.Semiformula.Operator.operator,
    FirstOrder.Semiformula.lMap_subst, FirstOrder.Semiformula.lMap_emb, ← lMap_eqSentence,
    Function.comp_def, Matrix.comp_vecCons', Matrix.constant_eq_singleton, toLX_rel,
    toLX_func]

/-- The image of a transported `𝗘𝗤 ℒₒᵣ`-axiom. -/
private theorem image_eq_of_mem (ψ : Semiformula ℒₒᵣ ℕ Empty 0 1)
    {σ₀ : FirstOrder.Sentence ℒₒᵣ} (h : σ₀ ∈ 𝗘𝗤 ℒₒᵣ) :
    Provable ACA (toSOAt ψ (FirstOrder.Rewriting.emb
      (FirstOrder.Semiformula.lMap toLX σ₀))) := by
  rw [toSOAt_lMap_sentence σ₀]
  exact provable_mono ACA₀_subset_ACA (ofAxiom (eqAxioms_subset_ACA₀ ⟨σ₀, h, rfl⟩))

/-- **The congruence statement for `ψ`**: the `toSOAt`-image of `𝗘𝗤 LX`'s
extensionality axiom for the fresh predicate `X`.  Spelled out, it is
`∀x∀y (x = y → ψ(x) → ψ(y))`; this is the *only* axiom of `paLX` whose image is
not already an axiom of `ACA` (for `ψ` an atom it is `setExt`; in general it is
proved by induction on `ψ`). -/
def CongruenceStatement (ψ : Semiformula ℒₒᵣ ℕ Empty 0 1) : Proposition ℒₒᵣ :=
  toSOAt ψ (FirstOrder.Rewriting.emb
    (FirstOrder.Theory.Eq.relExt (L := LX) (Sum.inr XRel.X)))

/-- **The image of `𝗘𝗤 LX`**, given congruence for `ψ`. -/
theorem image_eqLX (ψ : Semiformula ℒₒᵣ ℕ Empty 0 1)
    (hcong : Provable ACA (CongruenceStatement ψ)) {σ : FirstOrder.Sentence LX}
    (h : σ ∈ 𝗘𝗤 LX) : Provable ACA (toSOAt ψ (FirstOrder.Rewriting.emb σ)) := by
  cases h with
  | refl => rw [lMap_eq_refl]; exact image_eq_of_mem ψ FirstOrder.Theory.eqAxiom.refl
  | symm => rw [lMap_eq_symm]; exact image_eq_of_mem ψ FirstOrder.Theory.eqAxiom.symm
  | trans => rw [lMap_eq_trans]; exact image_eq_of_mem ψ FirstOrder.Theory.eqAxiom.trans
  | funcExt f =>
      match f with
      | Sum.inl f =>
          rw [lMap_eq_funcExt f]
          exact image_eq_of_mem ψ (FirstOrder.Theory.eqAxiom.funcExt f)
      | Sum.inr e => exact e.elim
  | relExt r =>
      match r with
      | Sum.inl r =>
          rw [lMap_eq_relExt r]
          exact image_eq_of_mem ψ (FirstOrder.Theory.eqAxiom.relExt r)
      | Sum.inr XRel.X => exact hcong

/-! ### Congruence

`Congruence.lean` proves the general Leibniz congruence for an arbitrary
second-order formula, in sequent form; all that is left is to identify
`CongruenceStatement ψ` with the `∀¹`-closed implication it produces. -/

private theorem emb_allClosure : ∀ {n : ℕ} (σ : FirstOrder.Semiformula LX Empty n),
    (FirstOrder.Rewriting.emb (∀¹* σ) : FirstOrder.Proposition LX) =
      ∀¹* (FirstOrder.Rewriting.emb σ)
  |       0, _ => rfl
  | (_ + 1), σ => by
      have h : (FirstOrder.Rewriting.emb (∀¹ σ) : FirstOrder.Semiformula LX ℕ _) =
          ∀¹ (FirstOrder.Rewriting.emb σ) := by
        show FirstOrder.Rew.emb ▹ (∀¹ σ) = _
        simp [FirstOrder.Rew.q_emb]
      exact (emb_allClosure (∀¹ σ)).trans
        (congrArg (fun x => (∀¹* x : FirstOrder.Proposition LX)) h)

/-- **`CongruenceStatement ψ`, spelled out**: `∀x∀y ((x = y ⋏ ⊤) → ψ(x) → ψ(y))`.
The stray `⊤` is Foundation's `Matrix.conj` over the single argument of `X`. -/
theorem congruenceStatement_eq (ψ : Semiformula ℒₒᵣ ℕ Empty 0 1) :
    CongruenceStatement ψ =
      allNums ((((eqA (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) #1) ⋏ ⊤) 🡒
        (((FirstOrder.Rewriting.emb ψ : Semiproposition ℒₒᵣ 0 1)/[(#0 :
            FirstOrder.Semiterm ℒₒᵣ ℕ 2)]) 🡒
          ((FirstOrder.Rewriting.emb ψ : Semiproposition ℒₒᵣ 0 1)/[(#1 :
            FirstOrder.Semiterm ℒₒᵣ ℕ 2)])))) := by
  show toSOAtB ψ (FirstOrder.Rewriting.emb
    (FirstOrder.Theory.Eq.relExt (L := LX) (Sum.inr XRel.X))) = _
  rw [show (FirstOrder.Theory.Eq.relExt (L := LX) (Sum.inr XRel.X)) =
      ∀¹* ((Matrix.conj fun i : Fin 1 =>
          (FirstOrder.Semiformula.Operator.Eq.eq (L := LX)).operator
            ![#(Fin.addCast 1 i), #(Fin.addNat i 1)]) 🡒
        ((FirstOrder.Semiformula.rel (Sum.inr XRel.X)
            (fun i : Fin 1 => #(Fin.addCast 1 i)) : FirstOrder.Semisentence LX 2) 🡒
          FirstOrder.Semiformula.rel (Sum.inr XRel.X) (fun i : Fin 1 => #(Fin.addNat i 1)))) from
    rfl, emb_allClosure, toSOAtB_allClosure]
  congr 1
  have e0 : (fun i : Fin 1 => (#(Fin.addCast 1 i) : FirstOrder.Semiterm LX Empty 2)) =
      ![#0] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi; rfl
  have e1 : (fun i : Fin 1 => (#(Fin.addNat i 1) : FirstOrder.Semiterm LX Empty 2)) =
      ![#1] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi; rfl
  have ac : Fin.addCast 1 (0 : Fin 1) = (0 : Fin 2) := rfl
  have an : Fin.addNat (0 : Fin 1) 1 = (1 : Fin 2) := rfl
  simp only [Matrix.conj, Matrix.vecTail, Matrix.cons_val_zero, ac, an,
    FirstOrder.Semiformula.Operator.eq_def, e0, e1]
  have hEqAtom : toSOAtB ψ (FirstOrder.Rewriting.emb
      (FirstOrder.Semiformula.rel FirstOrder.Language.Eq.eq
        ![(#0 : FirstOrder.Semiterm LX Empty 2), #1])) =
      eqA (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) #1 := by
    show (Semiformula.rel FirstOrder.Language.Eq.eq
      (fun i => unTerm (FirstOrder.Rew.emb (![(#0 : FirstOrder.Semiterm LX Empty 2), #1] i))) :
        Semiproposition ℒₒᵣ 0 2) = _
    congr 1
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj; rfl
  have hX0 : toSOAtB ψ (FirstOrder.Rewriting.emb
      (FirstOrder.Semiformula.rel (Sum.inr XRel.X : LX.Rel 1)
        ![(#0 : FirstOrder.Semiterm LX Empty 2)])) =
      (FirstOrder.Rewriting.emb ψ : Semiproposition ℒₒᵣ 0 1)/[(#0 :
        FirstOrder.Semiterm ℒₒᵣ ℕ 2)] := rfl
  have hX1 : toSOAtB ψ (FirstOrder.Rewriting.emb
      (FirstOrder.Semiformula.rel (Sum.inr XRel.X : LX.Rel 1)
        ![(#1 : FirstOrder.Semiterm LX Empty 2)])) =
      (FirstOrder.Rewriting.emb ψ : Semiproposition ℒₒᵣ 0 1)/[(#1 :
        FirstOrder.Semiterm ℒₒᵣ ℕ 2)] := rfl
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_top, toSOAtB_imply, toSOAtB_and, toSOAtB_verum]
  rw [hEqAtom, hX0, hX1]

/-- **Congruence.**  `ACA` proves `∀x∀y (x = y → ψ(x) → ψ(y))` for an arbitrary
second-order `ψ`. -/
theorem congruence (ψ : Semiformula ℒₒᵣ ℕ Empty 0 1) :
    Provable ACA (CongruenceStatement ψ) := by
  rw [congruenceStatement_eq]
  set A : Proposition ℒₒᵣ :=
    (FirstOrder.Rewriting.emb ψ : Semiproposition ℒₒᵣ 0 1)/[(&0 :
      FirstOrder.Semiterm ℒₒᵣ ℕ 0)] with hA
  set B : Proposition ℒₒᵣ :=
    (FirstOrder.Rewriting.emb ψ : Semiproposition ℒₒᵣ 0 1)/[(&1 :
      FirstOrder.Semiterm ℒₒᵣ ℕ 0)] with hB
  have hbase : PSeq ACA [(∼A), B, ∼(eqA (&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) &1)] := by
    have h := congrPSeq (FirstOrder.Rewriting.emb ψ : Semiproposition ℒₒᵣ 0 1)
      (FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)])
      (FirstOrder.Rew.subst ![(&1 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)]) (fun _ => rfl)
    have he : eqHyps (FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)])
        (FirstOrder.Rew.subst ![(&1 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)]) =
        [∼(eqA (&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) &1)] := by
      show List.ofFn (fun i : Fin 1 => _) = _
      rw [List.ofFn_succ]
      simp
    rw [he] at h
    exact h
  have h1 : PSeq ACA [(A 🡒 B), ∼(eqA (&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) &1)] :=
    PSeq.or hbase
  have h2 : PSeq ACA [(∼(eqA (&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) &1)),
      (⊥ : Proposition ℒₒᵣ), A 🡒 B] :=
    PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h1
  have h3 : PSeq ACA [((∼(eqA (&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) &1)) ⋎ ⊥), A 🡒 B] :=
    PSeq.or h2
  have h4 : Provable ACA (((eqA (&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) &1) ⋏ ⊤) 🡒 (A 🡒 B)) :=
    PSeq.to_provable (PSeq.or h3)
  have hcomp : ((FirstOrder.Rew.free.comp (FirstOrder.Rew.free.q)) :
      FirstOrder.Rew ℒₒᵣ ℕ 2 ℕ 0) =
      FirstOrder.Rew.free.comp (FirstOrder.Rew.free.q) := rfl
  refine gen₁ ACA_shift₀_invariant (gen₁ ACA_shift₀_invariant ?_)
  show Provable ACA (FirstOrder.Rew.free ▹ (FirstOrder.Rew.free.q ▹
    ((((eqA (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) #1) ⋏ ⊤) 🡒
      (((FirstOrder.Rewriting.emb ψ : Semiproposition ℒₒᵣ 0 1)/[(#0 :
          FirstOrder.Semiterm ℒₒᵣ ℕ 2)]) 🡒
        ((FirstOrder.Rewriting.emb ψ : Semiproposition ℒₒᵣ 0 1)/[(#1 :
          FirstOrder.Semiterm ℒₒᵣ ℕ 2)]))))))
  rw [← FirstOrder.TransitiveRewriting.comp_app]
  have hb0 : (FirstOrder.Rew.free.comp (FirstOrder.Rew.free.q))
      (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) = (&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) := by
    simp [FirstOrder.Rew.comp_app]
  have hfl : FirstOrder.Rew.free (#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) =
      (&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) := rfl
  have hb1 : (FirstOrder.Rew.free.comp (FirstOrder.Rew.free.q))
      (#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) = (&1 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) := by
    simp [FirstOrder.Rew.comp_app, hfl]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_top, Semiformula.rew_rel, emb_subst_rew, hb0, hb1]
  have hv : (fun i : Fin 2 => (FirstOrder.Rew.free.comp (FirstOrder.Rew.free.q))
      (![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2), #1] i)) =
      ![(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0), &1] := by
    funext i
    cases i using Fin.cases with
    | zero => exact hb0
    | succ j =>
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj; exact hb1
  rw [show (Semiformula.rel FirstOrder.Language.Eq.eq
      (fun i : Fin 2 => (FirstOrder.Rew.free.comp (FirstOrder.Rew.free.q))
        (![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2), #1] i)) : Proposition ℒₒᵣ) =
      eqA (&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) &1 from by rw [hv]]
  exact h4

/-! ### The capstone

Two blocks of `paLX` are discharged outright above, `LiftInduction.lean`
discharges the third (`image_indScheme`), and `congruence` discharges the
extensionality axiom of `𝗘𝗤 LX` for the fresh predicate.  The only remaining
hypotheses are the ones the assembly actually has: arithmetical witnesses for the
set parameters. -/

/-- **`lift_paLX`.**  Every `paLX`-theorem's `toSOAt`-image is `ACA`-provable,
at every parameter `ψ` whose set parameters are presented in bound slots and
then instantiated at arithmetical witnesses `Φ`. -/
theorem lift_paLX {N : ℕ} (ψ : Semiformula ℒₒᵣ ℕ Empty N 1)
    (hns : NoSetFvar (FirstOrder.Rewriting.emb ψ : Semiproposition ℒₒᵣ N 1))
    (Φ : Fin N → Semiformula ℒₒᵣ ℕ Empty 0 1)
    (hΦ : ∀ i, Arith (FirstOrder.Rewriting.emb (Φ i) : Semiformula ℒₒᵣ ℕ ℕ 0 1))
    {σ : FirstOrder.Sentence LX} (h : paLX ⊢ σ) :
    Provable ACA (toSOAt (Semiproposition.subst₁ ψ Φ) (FirstOrder.Rewriting.emb σ)) := by
  refine lift_of_axiomImages _ (fun τ hτ => ?_) h
  rcases hτ with hτ | hτ | hτ
  · exact image_eqLX _ (congruence _) hτ
  · exact image_paMinus _ hτ
  · obtain ⟨φ, -, rfl⟩ := hτ
    exact image_indScheme ψ hns Φ hΦ φ

/-- **`lift_paLX₀`**, the `N = 1` convenience form C1/C5 use: for *any*
arithmetical `ψ` (free set variables allowed — `#0 ∈& 0`, `Jump(X₀)`, …), the
`toSOAt ψ`-image of every `paLX`-theorem is `ACA`-provable.  The bound-slot
presentation is `#0 ∈# 0`, whose substitution instance at `ψ` is `ψ`. -/
theorem lift_paLX₀ (ψ : Semiformula ℒₒᵣ ℕ Empty 0 1)
    (hψ : Arith (FirstOrder.Rewriting.emb ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1))
    {σ : FirstOrder.Sentence LX} (h : paLX ⊢ σ) :
    Provable ACA (toSOAt ψ (FirstOrder.Rewriting.emb σ)) := by
  have e : Semiproposition.subst₁
      (((#0 : FirstOrder.Semiterm ℒₒᵣ Empty 1) ∈# (0 : Fin 1)) :
        Semiformula ℒₒᵣ ℕ Empty 1 1) ![ψ] = ψ := by
    show (SecondOrder.Rew.subst ![ψ]).app
      (((#0 : FirstOrder.Semiterm ℒₒᵣ Empty 1) ∈# (0 : Fin 1)) :
        Semiformula ℒₒᵣ ℕ Empty 1 1) = _
    simp only [SecondOrder.Rew.app_bvar, SecondOrder.Rew.subst_bv, Matrix.cons_val_fin_one]
    exact FirstOrder.Rewriting.subst1_bvar0_eq _
  have h2 := lift_paLX (N := 1)
    (((#0 : FirstOrder.Semiterm ℒₒᵣ Empty 1) ∈# (0 : Fin 1)) :
      Semiformula ℒₒᵣ ℕ Empty 1 1)
    (by simp) ![ψ] (fun i => by
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi; simpa using hψ) h
  rwa [e] at h2

end OrdinalAnalysis.ACA
