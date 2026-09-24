/-
  The Feferman-Schutte theorem for the semiformal ramified calculus `RA_∞`,
  in Schutte's formulation: autonomy of every notation below `Γ₀`, and the bound.

  ## The calculus

  `OmegaDerivableR junkLitsR evInstR ρ h Γ` (`Ramified/Calculus.lean`): the
  semiformal ramified calculus with the ω-rule over numerals, levels ranging over
  `Gamma0Note`, atomic axioms the true arithmetic literals together with the junk
  literals (a name that is not a `Good` code of a level denotes, at that level, the
  empty set), cut rank `ρ` and height `h`.  A formula of level `< ℓ` has rank
  `< blk ℓ` for a limit `ℓ` (`rank_lt_blk_of_lvlOf_lt`), so "cut rank below `blk λ`"
  is "cuts on formulas of levels below `λ`".

  ## Transfinite induction along an initial segment

  `tiSegR a :≡ TI(≺_a, X) :≡ Prog(≺_a, X) → ∀x X(x)`, with `y ≺_a x :≡ y ≺₁ x ∧ x ≺₁ ā`:
  transfinite induction for the free predicate `X` along the coded Veblen ordering
  restricted to the notations below `a`.  The lower bounds of
  `Ramified/SemiformalLower.lean` refute sentences of exactly this shape
  (`vebSegOrderR`'s ordering is `precBelowR` at its bound).

  ## Autonomy

  `SF λ H a`: some derivation of `TI(≺_a, X)` has cut rank below `blk λ` and height
  below `H`.  `Aut` is the inductive predicate

  * `base`: every `a < ε₀` is autonomous;
  * `step`: if every `b < λ` is autonomous and `SF λ λ a`, then `a` is autonomous.

  So heights and levels admitted at a stage are bounded by a notation `λ` all of
  whose predecessors have already been reached.  The height bound is essential: with
  unbounded heights `TI(≺_a, X)` is cut-free derivable for every `a` by climbing the
  well-ordering with the ω-rule, and the closure would be trivial.

  ## The proof of autonomy

  * **Stage 0** (`sf_stage0`).  Every derivation built from the generalised descent
    has height at least `ε₀`, so the first step, at `λ = ε₀`, uses an embedded
    finitary proof: `RAlt 2` proves `TI(≺_a, X)` for `a < φ_1(ε₀)`
    (`level_one_M`), and the embedding has height below `ε₀` and cut rank below
    `blkTop 2 < blk ε₀`.  So every `a < φ_1(ε₀)` is autonomous.
  * **The step** (`sf_step`).  Let `λ > ε₀` be a fixed point of `ω^·` all of whose
    predecessors are autonomous, and `a < φ_λ(0)`.  Since `λ` is a limit,
    `a < φ_β(0)` for some `β < λ` (`limitCover_zero`).  At the level `L = ω^β`,
    `(D^β)` (`descentBeta`) takes the trivial `Acc_{L+1}(0)` (`accZeroD`) to
    `Acc_L(φ_{1+β}(0))`, and the finitary implication
    `Acc_L(v) → TI(≺_a, X)` for `a ≤ v` (`tiSeg_acc_provable`) finishes.  The levels
    used are below `L + 3 < λ`, and the height `hgtD (1+β) ⊕ 3` stays below `λ`
    (`hgtD_lt_of_fixed`).  So every `a < φ_λ(0)` is autonomous.
  * **The recursion** (`aut_all`).  Along `λ_0 = ε₀`, `λ_{n+1} = φ_{λ_n}(0)`
    (`Gamma0Note.lam`), which exhausts `Gamma0Note` (`lt_lam`): everything below
    `λ_1 = φ_{ε₀}(0) ≤ φ_{φ_1(ε₀)}(0)` is reached from stage 0 by one step, and
    everything below `λ_{n+2} = φ_{λ_{n+1}}(0)` from everything below `λ_{n+1}` by
    one step, `λ_{n+1}` being a fixed point of `ω^·` above `ε₀`.

  ## The theorem

  `feferman_schutte`: every notation below `Γ₀` is autonomous, and no derivation with
  cut rank and height below `Γ₀` proves transfinite induction along the whole coded
  Veblen ordering `gamma0OrderR` (`fs_lower_junk`).  Both halves concern the same
  calculus, with the junk literals.  The arithmetic literals are among the junk
  literals, so the bound also holds without them (`fs_lower`); the autonomy half
  needs them, since the effective-level step of `(D^β)` reads a non-`Good` name as
  the empty set.

  This is a theorem about the semiformal calculus with levels below `Γ₀`.  It is not
  the proof-theoretic ordinal of a finitary theory: the finitary ramified theory
  with all finite levels is analysed in `Ramified/LimitTheorem.lean`, at `φ_2(0)`,
  and it is not a statement about `ATR₀`.
-/
import OrdinalAnalysis.Ramified.DescentBeta
import OrdinalAnalysis.Ramified.FSLower
import OrdinalAnalysis.Ramified.UpperBound
import OrdinalAnalysis.Ordinal.Veblen.VeblenCover

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

theorem le_onePlusNote_self (β : Gamma0Note) : β ≤ Gamma0Note.onePlusNote β := by
  rw [Gamma0Note.le_def, Gamma0Note.repr_onePlusNote]
  exact le_add_self

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)

/-! ### Transfinite induction along an initial segment -/

/-- **`TI(≺_a, X) :≡ Prog(≺_a, X) → ∀x X(x)`**, where `y ≺_a x :≡ y ≺₁ x ∧ x ≺₁ ā`. -/
def tiSegR (a : Gamma0Note) : Proposition LRA := TIR (precBelowR a)

theorem freeVariables_precBelowR (a : Gamma0Note) : (precBelowR a).freeVariables = ∅ := by
  have h : (precAt precCode₁R (#1 : Semiterm LRA ℕ 2)
      (numAtR (gamma0Code a) : Semiterm LRA ℕ 2)).freeVariables = ∅ :=
    freeVariables_precAt_eq_empty precCode₁R freeVariables_precCode₁R (by simp) (by simp)
  simp [precBelowR, h]

theorem freeVariables_tiSegR (a : Gamma0Note) : (tiSegR a).freeVariables = ∅ :=
  freeVariables_TIR _ (freeVariables_precBelowR a)

theorem lvlOf_tiSegR (a : Gamma0Note) : lvlOf (tiSegR a) = 0 := by
  simp [tiSegR, TIR, Prog, below, precAt, precBelowR, precCode₁R, lvlOf_lMap_toLRA]

section Model

variable {M : Type} [Nonempty M] [s : Structure LRA M] [Structure.Eq LRA M] {ν : Lv}

omit [Nonempty M] [Structure.Eq LRA M] in
/-- Reading `TI(≺_a, X)` in a model, in the direction used. -/
theorem eval_tiSegR_of (a : Gamma0Note) (f : ℕ → M)
    (h : (∀ x : M, (∀ y : M, precM y x ∧ precM x (numVal M (gamma0Code a)) → XM y) → XM x) →
      ∀ x : M, XM x) :
    Semiformula.Eval (s := s) ![] f (tiSegR a) := by
  simp only [tiSegR, TIR, Prog, below, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, Semiformula.eval_all, LogicalConnective.Prop.or_eq,
    LogicalConnective.Prop.neg_eq, eval_precAt_model, eval_Xat_model, Semiterm.val_bvar,
    eval_precBelowR, Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases hprog : ∀ x : M,
      (∀ y : M, precM y x ∧ precM x (numVal M (gamma0Code a)) → XM y) → XM x
  · exact Or.inr (h hprog)
  · refine Or.inl fun hall => hprog fun x hx => ?_
    rcases hall x with h1 | h1
    · exact absurd (fun y => imp_iff_not_or.mp (hx y)) h1
    · exact h1

/-- **`TI_κ(v̄)` gives `TI(≺_a, X)` for `a ≤ v`**, in a model of `RAlt ν`, `0 < κ < ν`:
level `κ` names `{y | y ≺₁ ā → X(y)}`, which is `≺₁`-progressive when `X` is
`≺_a`-progressive; and `X` holds outright at every `x` not below `a`. -/
theorem tiSeg_M (hM : M↓[LRA] ⊧* RAlt ν) {κ : Lv} (hκ0 : 0 < κ) (hκ : κ < ν)
    {a v : Gamma0Note} (hav : a ≤ v) (hacc : TImu κ (numVal M (gamma0Code v))) :
    (∀ x : M, (∀ y : M, precM y x ∧ precM x (numVal M (gamma0Code a)) → XM y) → XM x) →
      ∀ x : M, XM x := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos (lt_trans hκ0 hκ)
  have hshape : Shape κ (segGuardR a) :=
    shape_of_lvlOf_lt (by rw [lvlOf_segGuardR]; exact hκ0)
  obtain ⟨w, hw⟩ := comprM hM hκ0 hκ hshape (Classical.arbitrary M)
  have hG : ∀ x, memM κ x w ↔ (precM x (numVal M (gamma0Code a)) → XM x) := fun x =>
    (hw x).trans (eval_segGuardR _ x _)
  have hTI := (TIupM_congr hG _).mp (hacc w)
  intro hprog x
  have hprogG : ProgM (fun x : M => precM x (numVal M (gamma0Code a)) → XM x) :=
    fun x hx hxA => hprog x fun y hy => hx y hy.1 (precM_trans hM hν hy.1 hxA)
  by_cases hxA : precM x (numVal M (gamma0Code a))
  · have hxV : precM x (numVal M (gamma0Code v)) := by
      rcases lt_or_eq_of_le hav with hlt | heq
      · exact precM_trans hM hν hxA (precM_code hM hν hlt)
      · rw [← heq]; exact hxA
    exact hTI hprogG x hxV hxA
  · exact hprog x fun y hy => absurd hy.2 hxA

end Model

/-- **`RAlt ν ⊢ Acc_κ(v̄) → TI(≺_a, X)`** for `a ≤ v` and `0 < κ < ν`. -/
theorem tiSeg_acc_provable {ν κ : Lv} (hκ0 : 0 < κ) (hκ : κ < ν) {a v : Gamma0Note}
    (hav : a ≤ v) :
    RAlt ν ⊢ Semiformula.univCl (∼accA κ (gamma0Code v) ⋎ tiSegR a) := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos (lt_trans hκ0 hκ)
  have hc : (∼accA κ (gamma0Code v) ⋎ tiSegR a).freeVariables = ∅ := by
    rw [Semiformula.freeVariables_or, Semiformula.freeVariables_not, freeVariables_accA,
      freeVariables_tiSegR, Finset.union_empty]
  refine provable_of_eqModels hν ?_ ?_
  · rw [emb_univCl_of_freeVariables_eq_empty hc, lvlOf_or, lvlOf_neg, lvlOf_tiSegR]
    exact max_lt (lt_of_le_of_lt (lvlOf_accA_le κ _) hκ)
      (lt_of_lt_of_le Gamma0Note.zero_lt_one hν)
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f (∼accA κ (gamma0Code v) ⋎ tiSegR a)
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, eval_accA]
    by_cases h : TImu κ (numVal N (gamma0Code v))
    · exact Or.inr (eval_tiSegR_of a f (tiSeg_M hN hκ0 hκ hav h))
    · exact Or.inl h

theorem one_lt_ofNat_two : (1 : Lv) < Gamma0Note.ofNat 2 := by
  rw [← Gamma0Note.ofNat_one]; exact Gamma0Note.ofNat_lt_ofNat (by norm_num)

/-- **`RAlt 2 ⊢ TI(≺_a, X)` for `a < φ_1(ε₀)`.** -/
theorem tiSeg_stage0_provable {a : Gamma0Note}
    (ha : a < OmegaDerivableR.veblenIter 1 1 (Gamma0Note.epsilonNote 0)) :
    RAlt (Gamma0Note.ofNat 2) ⊢ Semiformula.univCl (tiSegR a) := by
  have hν : 1 ≤ Gamma0Note.ofNat 2 := one_lt_ofNat_two.le
  refine provable_of_eqModels hν ?_ ?_
  · rw [emb_univCl_of_freeVariables_eq_empty (freeVariables_tiSegR a), lvlOf_tiSegR]
    exact lt_of_lt_of_le Gamma0Note.zero_lt_one hν
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    obtain ⟨c, hc, hac⟩ := exists_lt_veblenIter 1 a ha
    have h1 := level_one_M (ν := 1) hN le_rfl hc
    exact eval_tiSegR_of a f (tiSeg_M hN Gamma0Note.zero_lt_one one_lt_ofNat_two hac.le h1)

/-! ### Autonomy -/

/-- **Levels below a limit `λ` are ranks below `blk λ`**: a formula of level `< λ` is a
legitimate cut formula at every cut rank `≥ blk λ`, when `λ` is closed under `· ⊕ 1`. -/
theorem rank_lt_blk_of_lvlOf_lt {n : ℕ} {lam : Lv}
    (hlim : ∀ μ : Lv, μ < lam → Gamma0Note.nadd μ 1 < lam) {φ : Semiformula LRA ℕ n}
    (h : lvlOf φ < lam) : rank φ < Gamma0Note.blk lam :=
  lt_of_lt_of_le (rank_lt_of_lvlOf_le le_rfl) (Gamma0Note.blkTop_le_blk (hlim _ h))

/-- **`SF λ H a`**: transfinite induction along the segment below `a`, for the free
predicate `X`, has a derivation in `RA_∞` (with the junk literals) of cut rank below
`blk λ` (levels below `λ`) and height below `H`. -/
def SF (lam H a : Gamma0Note) : Prop :=
  ∃ ρ h : Gamma0Note, ρ < Gamma0Note.blk lam ∧ h < H ∧
    OmegaDerivableR junkLitsR evInstR ρ h [evR (tiSegR a)]

/-- **The autonomous notations.**  `Aut a`: the notation `a` is reached by the
autonomous closure.

* `base`: every `a < ε₀`.
* `step`: if every `b < λ` is already reached, then every `a` such that `TI(≺_a, X)`
  (`tiSegR a`) is derivable in the semiformal ramified calculus `RA_∞` with the junk
  literals, at a cut rank below `blk λ` (levels below `λ`) and a height below `λ`
  (`SF λ λ a`), is reached.

The quantification in `step` is over notations `λ : Gamma0Note` and over derivations
of the calculus `OmegaDerivableR junkLitsR evInstR`; nothing else is assumed.  The
heights and levels admitted at a stage are bounded by a notation all of whose
predecessors are reached, never arbitrary. -/
inductive Aut : Gamma0Note → Prop
  | base {a : Gamma0Note} : a < Gamma0Note.epsilonNote 0 → Aut a
  | step {lam a : Gamma0Note} : (∀ b : Gamma0Note, b < lam → Aut b) → SF lam lam a → Aut a

/-! ### Stage 0: the embedded finitary proof -/

theorem blkTop_two_lt_blk_epsilon :
    Gamma0Note.blkTop (Gamma0Note.ofNat 2) < Gamma0Note.blk (Gamma0Note.epsilonNote 0) := by
  have h3 : Gamma0Note.ofNat 3 ≠ 0 := ne_of_gt (ofNat_pos' (by norm_num))
  calc Gamma0Note.blkTop (Gamma0Note.ofNat 2)
      ≤ Gamma0Note.blk (Gamma0Note.ofNat 3) :=
        Gamma0Note.blkTop_le_blk (Gamma0Note.ofNat_lt_ofNat (by norm_num))
    _ < Gamma0Note.blkTop (Gamma0Note.ofNat 3) := Gamma0Note.blk_lt_blkTop h3
    _ ≤ Gamma0Note.blk (Gamma0Note.epsilonNote 0) :=
        Gamma0Note.blkTop_le_blk (ofNat_lt_epsilonNote_zero 3)

/-- **`SF(ε₀, ε₀, a)` for `a < φ_1(ε₀)`**, by embedding the `RAlt 2`-proof. -/
theorem sf_stage0 {a : Gamma0Note}
    (ha : a < OmegaDerivableR.veblenIter 1 1 (Gamma0Note.epsilonNote 0)) :
    SF (Gamma0Note.epsilonNote 0) (Gamma0Note.epsilonNote 0) a := by
  obtain ⟨α, hα, d⟩ := DerLt.of_RAlt one_lt_ofNat_two.le (freeVariables_tiSegR a)
    (tiSeg_stage0_provable ha) le_rfl le_rfl
  exact ⟨_, α, blkTop_two_lt_blk_epsilon, hα, d⟩

/-- Every `a < φ_1(ε₀)` is autonomous. -/
theorem aut_stage0 {a : Gamma0Note}
    (ha : a < OmegaDerivableR.veblenIter 1 1 (Gamma0Note.epsilonNote 0)) : Aut a :=
  Aut.step (fun _ hb => Aut.base hb) (sf_stage0 ha)

/-! ### The step: one application of `(D^β)` -/

section Step

variable {lam : Gamma0Note}

/-- A fixed point of `ω^·` is closed under `⊕`. -/
theorem nadd_lt_of_fixed (hlam : Gamma0Note.omegaPow lam = lam) {x y : Gamma0Note}
    (hx : x < lam) (hy : y < lam) : Gamma0Note.nadd x y < lam := by
  rw [← hlam]
  exact Gamma0Note.nadd_lt_omegaPow (hlam.symm ▸ hx) (hlam.symm ▸ hy)

/-- A positive fixed point of `ω^·` is a limit. -/
theorem isSuccLimit_of_fixed (hlam : Gamma0Note.omegaPow lam = lam) (h0 : 0 < lam) :
    Order.IsSuccLimit (Gamma0Note.repr lam) := by
  have hr : Gamma0Note.repr lam ≠ 0 := by
    intro h
    rw [Gamma0Note.lt_def, Gamma0Note.repr_zero, h] at h0
    exact lt_irrefl _ h0
  have h := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hr
  rwa [← Gamma0Note.repr_omegaPow, hlam] at h

/-- **The step.**  If `λ > ε₀` is a fixed point of `ω^·`, then `SF(λ, λ, a)` for every
`a < φ_λ(0)`. -/
theorem sf_step (hlam : Gamma0Note.omegaPow lam = lam) (hε : Gamma0Note.epsilonNote 0 < lam)
    {a : Gamma0Note} (ha : a < Gamma0Note.veblenNote lam 0) : SF lam lam a := by
  have h0 : (0 : Gamma0Note) < lam :=
    lt_of_le_of_lt (Gamma0Note.zero_le_note _) hε
  have hone : Gamma0Note.ofNat 1 < lam := lt_trans (ofNat_lt_epsilonNote_zero 1) hε
  obtain ⟨β, hβ, haβ⟩ := Gamma0Note.limitCover_zero (isSuccLimit_of_fixed hlam h0) ha
  -- the level `L = ω^β` and the levels above it
  set L : Gamma0Note := Gamma0Note.nadd 0 (Gamma0Note.omegaPow β) with hLdef
  set L1 : Gamma0Note := Gamma0Note.nadd L 1 with hL1def
  set L2 : Gamma0Note := Gamma0Note.nadd L1 1 with hL2def
  have hL0 : 0 < L := by rw [hLdef, Gamma0Note.zero_nadd]; exact Gamma0Note.omegaPow_pos β
  have hL : L < lam := by
    rw [hLdef, Gamma0Note.zero_nadd]
    have h := Gamma0Note.omegaPow_lt_omegaPow hβ
    rwa [hlam] at h
  have hone' : (1 : Gamma0Note) < lam := hone
  have hL1 : L1 < lam := nadd_lt_of_fixed hlam hL hone'
  have hL2 : L2 < lam := nadd_lt_of_fixed hlam hL1 hone'
  have hL3 : Gamma0Note.nadd L2 1 < lam := nadd_lt_of_fixed hlam hL2 hone'
  -- the cut rank
  set ρ : Gamma0Note := Gamma0Note.blkTop L2 with hρdef
  have hρlt : ρ < Gamma0Note.blk lam :=
    calc ρ ≤ Gamma0Note.blk (Gamma0Note.nadd L2 1) :=
          Gamma0Note.blkTop_le_blk (Gamma0Note.lt_nadd_one L2)
      _ < Gamma0Note.blkTop (Gamma0Note.nadd L2 1) :=
          Gamma0Note.blk_lt_blkTop (nadd_one_ne_zero L2)
      _ ≤ Gamma0Note.blk lam := Gamma0Note.blkTop_le_blk hL3
  have hρ1 : Gamma0Note.omegaPow 1 ≤ ρ := omegaPow_one_le_blkTop (nadd_one_ne_zero L1)
  have hρL1 : Gamma0Note.blkTop L1 ≤ ρ := Gamma0Note.blkTop_mono (Gamma0Note.lt_nadd_one L1).le
  -- the value reached
  set b1 : Gamma0Note := Gamma0Note.onePlusNote β with hb1def
  set v : Gamma0Note := Gamma0Note.veblenNote b1 0 with hvdef
  have hav : a ≤ v :=
    le_trans haβ.le (Gamma0Note.veblenNote_le_veblenNote_left (le_onePlusNote_self β))
  have hb1 : b1 < lam :=
    lt_of_le_of_lt (Gamma0Note.onePlusNote_le_nadd_one β) (nadd_lt_of_fixed hlam hβ hone')
  -- heights
  set H1 : Gamma0Note := Gamma0Note.nadd (hgtD b1) (Gamma0Note.ofNat 1) with hH1def
  set H2 : Gamma0Note := Gamma0Note.nadd H1 (Gamma0Note.ofNat 1) with hH2def
  set H3 : Gamma0Note := Gamma0Note.nadd H2 (Gamma0Note.ofNat 1) with hH3def
  have hH3 : H3 < lam :=
    nadd_lt_of_fixed hlam (nadd_lt_of_fixed hlam (nadd_lt_of_fixed hlam
      (hgtD_lt_of_fixed hlam hε hb1) hone) hone) hone
  have hεH1 : Gamma0Note.epsilonNote 0 ≤ H1 :=
    le_trans (eps_le_hgtD b1) (le_nadd_ofNat _ 1)
  -- `(D^β)`: `¬Acc_{L+1}(0), Acc_L(φ_{1+β}(0))`
  have hD : DerLt ρ [evR (∼accA L1 (gamma0Code 0)), evR (accA L (gamma0Code v))] H1 :=
    DerLt.of_der ((descentBeta β 0 (Gamma0Note.powClosed_zero β) 0).mono_rank hρL1)
      (lt_nadd_ofNat_one _)
  -- `Acc_{L+1}(0)`
  have hZ : DerLt ρ [evR (accA L1 (gamma0Code 0))] H1 :=
    (accZeroD (μ := L1) (Γ := []) hρ1 le_rfl le_rfl).mono
      (le_trans (eps_nadd_le_hgtD b1 6) (le_nadd_ofNat _ 1))
  -- `Acc_L(φ_{1+β}(0))`
  have hA : DerLt ρ [evR (accA L (gamma0Code v))] H2 :=
    transfer (lt_of_lt_of_le (rank_accA_lt le_rfl _) le_rfl) hD hZ (lt_nadd_ofNat_one _)
  -- `Acc_L(v̄) → TI(≺_a, X)`
  have hC : DerLt ρ [evR (∼accA L (gamma0Code v) ⋎ tiSegR a)] H2 := by
    have hc : (∼accA L (gamma0Code v) ⋎ tiSegR a).freeVariables = ∅ := by
      rw [Semiformula.freeVariables_or, Semiformula.freeVariables_not, freeVariables_accA,
        freeVariables_tiSegR, Finset.union_empty]
    exact DerLt.of_RAlt (Gamma0Note.one_le_nadd_one L) hc
      (tiSeg_acc_provable hL0 (Gamma0Note.lt_nadd_one L) hav) hρL1
      (le_trans hεH1 (le_nadd_ofNat _ 1))
  rw [evR_or] at hC
  have hC' := hC.invOr
  rw [evR_neg] at hC'
  have hrk : rank (evR (accA L (gamma0Code v))) < ρ := by
    rw [rank_evR]
    exact lt_of_lt_of_le (rank_accA_lt le_rfl _) (Gamma0Note.blkTop_mono
      (Gamma0Note.nadd_le_nadd_left 1 (Gamma0Note.lt_nadd_one L).le))
  obtain ⟨α, hα, d⟩ := DerLt.cutHyp hrk hC' hA (lt_nadd_ofNat_one H2)
  exact ⟨ρ, α, hρlt, lt_trans hα hH3, by simpa using d⟩

/-- **Everything below `φ_λ(0)` is autonomous** once everything below `λ` is, for a
fixed point `λ > ε₀` of `ω^·`. -/
theorem aut_of_fixed (hlam : Gamma0Note.omegaPow lam = lam)
    (hε : Gamma0Note.epsilonNote 0 < lam) (hall : ∀ b : Gamma0Note, b < lam → Aut b)
    {a : Gamma0Note} (ha : a < Gamma0Note.veblenNote lam 0) : Aut a :=
  Aut.step hall (sf_step hlam hε ha)

end Step

/-! ### The recursion over `λ_n` -/

theorem le_veblenNote_left (x y : Gamma0Note) : x ≤ Gamma0Note.veblenNote x y := by
  rw [Gamma0Note.le_def, Gamma0Note.repr_veblenNote]
  exact Ordinal.left_le_veblen _ _

theorem epsilon_le_lam : ∀ n : ℕ, Gamma0Note.epsilonNote 0 ≤ Gamma0Note.lam n
  | 0 => le_rfl
  | n + 1 => le_trans (epsilon_le_lam n) (le_veblenNote_left _ _)

theorem one_lt_epsilonNote_zero : (1 : Gamma0Note) < Gamma0Note.epsilonNote 0 :=
  ofNat_lt_epsilonNote_zero 1

/-- `λ_{n+1}` is a fixed point of `ω^·`. -/
theorem omegaPow_lam_succ (n : ℕ) :
    Gamma0Note.omegaPow (Gamma0Note.lam (n + 1)) = Gamma0Note.lam (n + 1) :=
  Gamma0Note.omegaPow_veblenNote (le_trans one_lt_epsilonNote_zero.le (epsilon_le_lam n)) 0

/-- `ε₀ < λ_{n+1}`. -/
theorem epsilon_lt_lam_succ (n : ℕ) : Gamma0Note.epsilonNote 0 < Gamma0Note.lam (n + 1) :=
  Gamma0Note.veblenNote_zero_lt_veblenNote_zero
    (lt_of_lt_of_le one_lt_epsilonNote_zero (epsilon_le_lam n))

/-- **Everything below `λ_{n+1}` is autonomous.** -/
theorem aut_lt_lam_succ : ∀ n : ℕ, ∀ a : Gamma0Note, a < Gamma0Note.lam (n + 1) → Aut a
  | 0, a, ha => by
      -- one step from stage 0, at the fixed point `φ_1(ε₀)`
      have e : OmegaDerivableR.veblenIter 1 1 (Gamma0Note.epsilonNote 0) =
          Gamma0Note.epsilonNote (Gamma0Note.epsilonNote 0) :=
        veblenIter_succ' 1 0 (Gamma0Note.epsilonNote 0)
      have hfix : Gamma0Note.omegaPow (Gamma0Note.epsilonNote (Gamma0Note.epsilonNote 0)) =
          Gamma0Note.epsilonNote (Gamma0Note.epsilonNote 0) :=
        Gamma0Note.omegaPow_epsilonNote _
      have hε : Gamma0Note.epsilonNote 0 < Gamma0Note.epsilonNote (Gamma0Note.epsilonNote 0) :=
        Gamma0Note.epsilon_lt_epsilon (Gamma0Note.epsilon_pos 0)
      refine aut_of_fixed hfix hε (fun b hb => aut_stage0 (e ▸ hb)) ?_
      exact lt_of_lt_of_le ha (Gamma0Note.veblenNote_le_veblenNote_left hε.le)
  | n + 1, a, ha =>
      aut_of_fixed (omegaPow_lam_succ n) (epsilon_lt_lam_succ n) (aut_lt_lam_succ n) ha

/-- **Every notation below `Γ₀` is autonomous.** -/
theorem aut_all (a : Gamma0Note) : Aut a := by
  obtain ⟨n, hn⟩ := Gamma0Note.lt_lam a
  exact aut_lt_lam_succ n a (lt_of_lt_of_le hn (le_veblenNote_left _ _))

/-! ### The theorem -/

/-- **The Feferman-Schutte theorem for `RA_∞`, in Schutte's formulation.**

* Every notation `a : Gamma0Note` (that is, every ordinal below `Γ₀`) is autonomous:
  `Aut a`, where `Aut` is generated by `a < ε₀` and by the step "if every `b < λ` is
  autonomous, every `a` with a derivation of `TI(≺_a, X)` of cut rank below `blk λ`
  (levels below `λ`) and height below `λ` is autonomous".
* No derivation of the same calculus with cut rank `ρ` and height `h` below `Γ₀`
  proves transfinite induction along the whole coded Veblen ordering `gamma0OrderR`.

The calculus is the semiformal ramified calculus with the ω-rule and levels below
`Γ₀`, with the junk literals among its axioms, in both halves.  This is not the
analysis of a finitary theory, and not a statement about `ATR₀`. -/
theorem feferman_schutte :
    (∀ a : Gamma0Note, Aut a) ∧
      ∀ ρ h : Gamma0Note,
        ¬ OmegaDerivableR junkLitsR evInstR ρ h [evR (TIR gamma0OrderR.prec)] :=
  ⟨aut_all, fs_lower_junk⟩

/-- The bound half for the calculus whose atomic axioms are the true arithmetic
literals only: its derivations are derivations with the junk literals, so it is a
consequence of `feferman_schutte`. -/
theorem feferman_schutte_bound_arith (ρ h : Gamma0Note) :
    ¬ OmegaDerivableR trueArithLitsR evInstR ρ h [evR (TIR gamma0OrderR.prec)] := fun hder =>
  feferman_schutte.2 ρ h (hder.mono_lits trueArithLitsR_le_junkLitsR)

/-! ### Axiom audit -/

#print axioms rank_lt_blk_of_lvlOf_lt
#print axioms tiSeg_acc_provable
#print axioms tiSeg_stage0_provable
#print axioms sf_stage0
#print axioms sf_step
#print axioms aut_all
#print axioms feferman_schutte
#print axioms feferman_schutte_bound_arith

end Ramified

end OrdinalAnalysis
