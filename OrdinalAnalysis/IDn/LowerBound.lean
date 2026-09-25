/-
  The lower bound for `IDn n (WForms orderFormulas n)`: transfinite induction along the
  multi-level ϑ-order up to `Omega 0`, read for the free predicate `X`, is not provable, given
  `EmbedHyps (WForms orderFormulas n)` (Freund's Theorem 6.5, per level) and one further
  composed fact not yet available anywhere on disk (`CollapseCorollary`, see its own docstring
  below).

  Source: A. Freund, arXiv:2204.09321, Corollary 7.2 / Proposition 5.8 / Theorem 5.9, lifted
  per level; `OrdinalAnalysis.ID1.LowerBound` is the one-level mirror (`not_derivable_fieldInI`,
  `id1_lower_bound_of_embedding_xfree`). This file documents the exact gap rather than silently
  assuming it away. `F := Upper.orderFormulas` throughout, matching
  `IDn/Internal/OrderBridge.lean`'s own fixed instance.

  **Scope note (2026-09-24).** `EmbedHypsDischarge.lean` (discharging
  `EmbedHyps` from `AxiomsLogic`/`AxiomsPA`/`AxiomsID`) is developed separately.
  This file takes `hyps : EmbedHyps (WForms orderFormulas n)` as an explicit hypothesis
  throughout.

  **The one remaining gap (`CollapseCorollary`).** `IDn/Collapsing/Theorem.lean`'s
  `collapse_zero_bound` needs an input cut rank of exactly `Collapsing.muBar m` for some
  `m ≤ n`; the largest such value is `muBar n = Omega (n - 1) + one`
  (`Collapsing.muBar_lt_Omega`: `muBar p < Omega p`). `IDn/Embed.lean`'s
  `embedding_theorem_xfree` instead produces a cut rank `OmegaPlus (n := n) m = Omega n +
  ofNat m` for an existentially-quantified `m : ℕ` — strictly above `Omega n`, hence strictly
  above every `muBar m'` for `m' ≤ n`. Bridging the two needs an `n`-fold induction crossing
  every `(Fix)`-level via `IDn/PredCut.lean`'s `predicative_cut_elim`, composed with
  `IDn/Elimination.lean`'s `elimination_iter` for the finite part; `IDn/Elimination.lean`'s own
  header says this composition ("the multi-level collapsing corollary ... Buchholz Theorem 4.8
  §2.4") **is not written yet** anywhere in the tree. Kept as an explicit hypothesis,
  `CollapseCorollary`, stated in exactly the shape `collapse_zero_bound` + `StageSem.sound`
  need it in (so that closing it later is a drop-in replacement, not a restatement of this
  file). Every other step in this file is a real proof against already-green library facts.

  Contents.

    `noXN_fieldInI0`, `xFreeL_of_noXN`, `xFreeL_fieldInI0`, `xFreeL_WForms`
                                       `X`-freeness of `fieldInI0`/`WForms`, for
                                       `embedding_theorem_xfree`'s own hypotheses
    `levelBounded_fieldInI0`, `positiveIn_fieldInI0`, `sigmaW_embed_fieldInI0`
                                       `embed (fieldInI0 …)` is `Σ(Ω_1)` (needed for
                                       `CollapseCorollary`'s own hypothesis)
    `CollapseCorollary`               the one open link, documented above
    `not_derivable_fieldInI0`         no derivation of the embedded sentence, given the two
                                       hypotheses
    `idn_lower_bound`                 the lower bound at the bound `Omega 0`
-/
import OrdinalAnalysis.IDn.LowerBoundAux2
import OrdinalAnalysis.IDn.Embed
import OrdinalAnalysis.IDn.Collapsing.Theorem

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.IDn.Upper
open OrdinalAnalysis.IDn.Internal (code)

variable {n : ℕ}

/-! ### `fieldInI0` mentions no `X`, and is `X`-free in `Evaluate.lean`'s sense -/

theorem noXN_fieldInI0 (F : OrderFormulas) (hn : 0 < n) (a : ThetaWNoteD) :
    NoXN (fieldInI0 F n hn a) :=
  (noXN_imp _ _).mpr ⟨noXN_lMap_toLXIN _, noXN_Iat _ _⟩

/-- `NoXN` (`IDn/LowerBoundAux.lean`) and `XFreeL` (`IDn/Evaluate.lean`) are the same recursive
predicate under two different names (one file predates the other's port); bridged here rather
than in either file, since neither file covers it. -/
theorem xFreeL_of_noXN {ξ : Type*} :
    ∀ {m : ℕ} (φ : Semiformula (LXIn n) ξ m), NoXN φ → XFreeL φ
  | _, .verum, _ => trivial
  | _, .falsum, _ => trivial
  | _, .rel (Sum.inl _) _, _ => trivial
  | _, .rel (Sum.inr (IXRelN.I _)) _, _ => trivial
  | _, .rel (Sum.inr IXRelN.X) _, h => h.elim
  | _, .nrel (Sum.inl _) _, _ => trivial
  | _, .nrel (Sum.inr (IXRelN.I _)) _, _ => trivial
  | _, .nrel (Sum.inr IXRelN.X) _, h => h.elim
  | _, .and φ ψ, h => ⟨xFreeL_of_noXN φ h.1, xFreeL_of_noXN ψ h.2⟩
  | _, .or φ ψ, h => ⟨xFreeL_of_noXN φ h.1, xFreeL_of_noXN ψ h.2⟩
  | _, .all φ, h => xFreeL_of_noXN φ h
  | _, .exs φ, h => xFreeL_of_noXN φ h

theorem xFreeL_fieldInI0 (F : OrderFormulas) (hn : 0 < n) (a : ThetaWNoteD) :
    XFreeL (fieldInI0 F n hn a) := xFreeL_of_noXN _ (noXN_fieldInI0 F hn a)

theorem xFreeL_WForms (F : OrderFormulas) (k : Fin n) : XFreeL (WForms F n k) :=
  xFreeL_of_noXN _ (noXN_wForm F k.pos k.val)

/-! ### `embed (fieldInI0 …)` is `Σ(Ω_1)` at level `0` -/

/-- `LevelBounded` is invariant under an arbitrary term rewriting (it only looks at the
relation symbols, never at terms) — the `LevelBounded` analogue of `Evaluate.xFreeI_rew` /
`Language.sigmaW_rew`, needed here to move `LevelBounded` across the `Sentence → Proposition`
coercion (`Rewriting.emb`). -/
theorem levelBounded_rew {ξ₁ ξ₂ : Type*} (k : Fin n) :
    ∀ {m₁ m₂ : ℕ} (ω : Rew (LXIn n) ξ₁ m₁ ξ₂ m₂) (φ : Semiformula (LXIn n) ξ₁ m₁),
      LevelBounded k (ω ▹ φ) ↔ LevelBounded k φ
  | _, _, _, .verum => Iff.rfl
  | _, _, _, .falsum => Iff.rfl
  | _, _, ω, .rel r v => by
      rw [Semiformula.rew_rel]
      rcases r with r | r
      · exact Iff.rfl
      · cases r <;> exact Iff.rfl
  | _, _, ω, .nrel r v => by
      rw [Semiformula.rew_nrel]
      rcases r with r | r
      · exact Iff.rfl
      · cases r <;> exact Iff.rfl
  | _, _, ω, .and φ ψ => by
      rw [show (Semiformula.and φ ψ) = φ ⋏ ψ from rfl, LogicalConnective.HomClass.map_and]
      exact and_congr (levelBounded_rew k ω φ) (levelBounded_rew k ω ψ)
  | _, _, ω, .or φ ψ => by
      rw [show (Semiformula.or φ ψ) = φ ⋎ ψ from rfl, LogicalConnective.HomClass.map_or]
      exact and_congr (levelBounded_rew k ω φ) (levelBounded_rew k ω ψ)
  | _, _, ω, .all φ => by
      rw [show (Semiformula.all φ) = ∀¹ φ from rfl, Rewriting.app_all]
      exact levelBounded_rew k ω.q φ
  | _, _, ω, .exs φ => by
      rw [show (Semiformula.exs φ) = ∃¹ φ from rfl, Rewriting.app_exs]
      exact levelBounded_rew k ω.q φ

/-- `PositiveIn` is invariant under an arbitrary term rewriting, for the same reason as
`levelBounded_rew`. -/
theorem positiveIn_rew {ξ₁ ξ₂ : Type*} (k : Fin n) :
    ∀ {m₁ m₂ : ℕ} (ω : Rew (LXIn n) ξ₁ m₁ ξ₂ m₂) (φ : Semiformula (LXIn n) ξ₁ m₁),
      PositiveIn k (ω ▹ φ) ↔ PositiveIn k φ
  | _, _, _, .verum => Iff.rfl
  | _, _, _, .falsum => Iff.rfl
  | _, _, ω, .rel r v => by
      rw [Semiformula.rew_rel]
      rcases r with r | r
      · exact Iff.rfl
      · cases r <;> exact Iff.rfl
  | _, _, ω, .nrel r v => by
      rw [Semiformula.rew_nrel]
      rcases r with r | r
      · exact Iff.rfl
      · cases r <;> exact Iff.rfl
  | _, _, ω, .and φ ψ => by
      rw [show (Semiformula.and φ ψ) = φ ⋏ ψ from rfl, LogicalConnective.HomClass.map_and]
      exact and_congr (positiveIn_rew k ω φ) (positiveIn_rew k ω ψ)
  | _, _, ω, .or φ ψ => by
      rw [show (Semiformula.or φ ψ) = φ ⋎ ψ from rfl, LogicalConnective.HomClass.map_or]
      exact and_congr (positiveIn_rew k ω φ) (positiveIn_rew k ω ψ)
  | _, _, ω, .all φ => by
      rw [show (Semiformula.all φ) = ∀¹ φ from rfl, Rewriting.app_all]
      exact positiveIn_rew k ω.q φ
  | _, _, ω, .exs φ => by
      rw [show (Semiformula.exs φ) = ∃¹ φ from rfl, Rewriting.app_exs]
      exact positiveIn_rew k ω.q φ

theorem levelBounded_fieldInI0 (F : OrderFormulas) (hn : 0 < n) (a : ThetaWNoteD) :
    LevelBounded (lvl0 hn) (fieldInI0 F n hn a) :=
  ⟨(levelBounded_lMap_toLXIN (lvl0 hn) (belowC F a)).2, le_refl _⟩

theorem positiveIn_fieldInI0 (F : OrderFormulas) (hn : 0 < n) (a : ThetaWNoteD) :
    PositiveIn (lvl0 hn) (fieldInI0 F n hn a) :=
  ⟨(positive_lMap_toLXIN (lvl0 hn) (belowC F a)).2, trivial⟩

theorem sigmaW_embed_fieldInI0 (F : OrderFormulas) (hn : 0 < n) (a : ThetaWNoteD) :
    SigmaW (lvl0 hn) (embed (fieldInI0 F n hn a : Proposition (LXIn n))) := by
  refine sigmaW_embed_iff (φ := (fieldInI0 F n hn a : Proposition (LXIn n))) ?_
    |>.mpr ?_
  · exact (levelBounded_rew (lvl0 hn) _ _).mpr (levelBounded_fieldInI0 F hn a)
  · exact (positiveIn_rew (lvl0 hn) _ _).mpr (positiveIn_fieldInI0 F hn a)

/-! ### The one open link -/

/-- **The multi-level collapsing corollary**, as a proposition (proved as
`IDn.collapseCorollary` in `IDn/CollapseCorollary.lean`). Stated in the shape
`Collapsing.collapse` + boundedness + `StageSem.sound` compose into: given a `Σ(Ω_1)`-formula `φ`
derivable at every nice operator with cut rank `OmegaPlus m` and height `OmegaTwo + ofNat r`
(`embedding_theorem_xfree`'s own conclusion shape), there is a stage `b` below `Omega 0` and a
nice operator `H` at which the capped sequent `[φ]` is derivable at cut rank and height `b`.
The operator is existential: Buchholz's Theorem 4.8 yields the pre-collapse hull `H_{α̂}`, not
the hull of the collapsed value `b`, and `StageSem.sound` is generic in the operator. -/
def CollapseCorollary (hn : 0 < n) : Prop :=
  ∀ {m r : ℕ} {φ : Proposition (LIinfN n)}, SigmaW (lvl0 hn) φ →
    (∀ H : Set ThetaWNoteD → Set ThetaWNoteD, ThetaWNoteD.NiceS H →
      IDnDerivable (WForms orderFormulas n) (OmegaPlus (n := n) m) H
        (OmegaTwo (n := n) + ThetaWNoteD.ofNat r) [φ]) →
    ∃ (b : StageAt (lvl0 hn).val) (H : Set ThetaWNoteD → Set ThetaWNoteD),
      ThetaWNoteD.NiceS H ∧ b.1 < ThetaWNoteD.Omega (lvl0 hn).val ∧
      IDnDerivable (WForms orderFormulas n) b.1 H b.1 (Collapsing.capSeq (lvl0 hn) b [φ])

/-! ### No derivation of the embedded sentence -/

/-- `belowC`'s meaning in the standard model of arithmetic, dropping the `mc`/level machinery
`Upper.eval_belowC` carries for a generic structure (not needed here: we evaluate directly at
`M := ℕ`, before any `lm`/`stdIN` wrapping). -/
theorem eval_belowC_nat (F : OrderFormulas) (a : ThetaWNoteD) (x : ℕ) :
    Semiformula.Eval (M := ℕ) ![x] Empty.elim (belowC F a) ↔
      F.fld x ∧ F.fld (code a.1 : ℕ) ∧ F.lt x (code a.1 : ℕ) := by
  unfold belowC
  rw [Semiformula.eval_substs]
  have e : (Semiterm.val (M := ℕ) ![x] Empty.elim ∘
      ![(#0 : Semiterm ℒₒᵣ Empty 1), ((code a.1 : ℕ) : Semiterm ℒₒᵣ Empty 1)])
        = ![x, (code a.1 : ℕ)] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => k.elim0) j
      simp
  rw [e]
  exact OrderFormulas.eval_precWDef F x _

/-- **The truth of `fieldInI0` in the stage-environment structure**: the direct analogue of
`LowerBoundAux2.lean`'s `codeAt0_mem_stageSetN_iff`'s own `hunfold`, but for `fieldInI0` (a bare
implication) rather than `wForm`'s closure-axiom shape. -/
theorem eval_fieldInI0_stdIN (hn : 0 < n) (P : ℕ → Prop) (S : Fin n → Set ℕ) (a : ThetaWNoteD) :
    Semiformula.Eval (s := stdIN P S) ![] Empty.elim
        (fieldInI0 orderFormulas n hn a) ↔
      ∀ x : ℕ, (orderFormulas.fld x ∧ orderFormulas.fld (code a.1 : ℕ) ∧
        orderFormulas.lt x (code a.1 : ℕ)) → x ∈ S (lvl0 hn) := by
  unfold fieldInI0
  rw [Semiformula.eval_all]
  refine forall_congr' fun x => ?_
  rw [LogicalConnective.HomClass.map_imply]
  have h1 : Semiformula.Eval (s := stdIN P S) ![x] Empty.elim
      (lm (belowC orderFormulas a)) ↔
      (orderFormulas.fld x ∧ orderFormulas.fld (code a.1 : ℕ) ∧
        orderFormulas.lt x (code a.1 : ℕ)) := by
    rw [lm, eval_lMap_toLXIN, eval_belowC_nat]
  have h2 : Semiformula.Eval (s := stdIN P S) ![x] Empty.elim
      (Iat (lvl0 hn) (#0 : Semiterm (LXIn n) Empty 1)) ↔ x ∈ S (lvl0 hn) := by
    rw [eval_Iat]
    simp
  rw [h1, h2]
  exact Iff.rfl

/-- **No derivation of the embedded `fieldInI0`, at the bound `Omega 0`**, given
`CollapseCorollary` (the exact analogue of `ID1.LowerBound.not_derivable_fieldInI`, via
`Collapsing.collapse_zero_bound` + `StageSem.sound` + `codeAt0_mem_stageSetN_iff`, composed here
by hypothesis instead of by a level-by-level induction not yet written). -/
theorem not_derivable_fieldInI0 (hn : 0 < n) (hcol : CollapseCorollary hn) {m r : ℕ}
    (d : ∀ H : Set ThetaWNoteD → Set ThetaWNoteD, ThetaWNoteD.NiceS H →
      IDnDerivable (WForms orderFormulas n) (OmegaPlus (n := n) m) H
        (OmegaTwo (n := n) + ThetaWNoteD.ofNat r)
        [embed (fieldInI0 orderFormulas n hn (ThetaWNoteD.Omega 0) : Proposition (LXIn n))]) :
    False := by
  obtain ⟨b, _, _, hbΩ, D⟩ :=
    hcol (sigmaW_embed_fieldInI0 orderFormulas hn (ThetaWNoteD.Omega 0)) d
  rw [Collapsing.capSeq_singleton] at D
  obtain ⟨φ, hφ, htrue⟩ :=
    StageSem.sound (fun _ => True) (WForms orderFormulas n) (wForms_levelBounded orderFormulas n)
      D hbΩ
  rw [List.mem_singleton.mp hφ] at htrue
  unfold StageSem.TrueSN at htrue
  rw [capAt_embed, Semiformula.eval_lMap, StageSem.lMap_stageHom_stageStrucN,
    Semiformula.eval_emb, eval_fieldInI0_stdIN] at htrue
  have hb1 : b.1 < ThetaWNoteD.Omega (lvl0 hn).val := hbΩ
  have hmem : (code b.1.1 : ℕ) ∈
      StageSem.stageEnvAt (StageSem.stageSetN (fun _ => True) (WForms orderFormulas n))
        (lvl0 hn) b (lvl0 hn) := by
    refine htrue (code b.1.1 : ℕ) ⟨(Internal.eval_fld_iff b.1.1).mpr b.1.2,
      (Internal.eval_fld_iff (ThetaWNoteD.Omega 0).1).mpr (ThetaWNoteD.Omega 0).2, ?_⟩
    exact (Internal.eval_lt_iff_lt b.1.1 (ThetaWNoteD.Omega 0).1).mpr hb1
  rw [StageSem.stageEnvAt, dif_pos rfl] at hmem
  have := (codeAt0_mem_stageSetN_iff hn (fun _ => True) b b.1).mp hmem
  exact lt_irrefl b.1 this

/-! ### The lower bound, at `Omega 0` -/

/-- **`IDn n (WForms orderFormulas n) ⊬ TI_{Ω_1}(≺, X)`**, given `EmbedHyps` and
`CollapseCorollary`. -/
theorem idn_lower_bound (hn : 0 < n) (hyps : EmbedHyps (WForms orderFormulas n))
    (hcol : CollapseCorollary hn) :
    ¬ IDn n (WForms orderFormulas n) ⊢ tiUptoSentence orderFormulas (Fin n) (ThetaWNoteD.Omega 0) := by
  intro h
  have hσ := provable_fieldInI0_of_ti orderFormulas hn h
  obtain ⟨m, r, hmr⟩ := embedding_theorem_xfree hyps (wForms_positive orderFormulas n)
    (xFreeL_WForms orderFormulas) (xFreeL_fieldInI0 orderFormulas hn (ThetaWNoteD.Omega 0)) hσ
  exact not_derivable_fieldInI0 hn hcol hmr

end IDn

end OrdinalAnalysis
