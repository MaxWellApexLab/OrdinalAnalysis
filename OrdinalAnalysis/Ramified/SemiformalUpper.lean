/-
  The semiformal analysis of ramified analysis at the principal levels `ω^γ`, `γ ≥ 1`:
  the upper halves, the sharp lower halves, and the two-sided theorem.

  Everything is stated in `RA_∞` with the junk literals (`OmegaDerivableR junkLitsR evInstR`),
  along the segment ordering below `φ_c(0)`,

      y ≺ x  :≡  y ≺₁ x ∧ x ≺₁ φ_c(0)‾      ((vebSegOrderR c 0 _).prec = precBelowR (φ_c(0))),

  for the free predicate `X`, with the two sentences

      TIR ≺         :≡  Prog(≺, X) → ∀y X(y),
      TIuptoR ≺ x̄   :≡  Prog(≺, X) → ∀y ≺ x̄, X(y)

  (the universal closure of `TIuptoR (precBelowR b) x̄` is `tiUptoSegR b x`).

  ## The value

  At the level `ω^γ` the value is `φ_{1+γ}(0)`, `1 + γ` genuine ordinal addition
  (`onePlusNote`): `φ_{n+1}(0)` at `γ = n`, `φ_γ(0)` at `γ ≥ ω`.  The cut ranks are those
  below `blk (ω^γ) = ω^{1+γ}` (`blk_omegaPow`).  All results are first proved at the Veblen
  index `a = 1 + γ > 1`, the level being `ω^{−1+a}` (`sf_theorem_index`).

  ## The upper half (`upper_index`, `sf_upper`)

  For `x < φ_a(0)`:

  * `a = a' ⊕ 1`: `x < φ_{a'}^m(0)` for some `m` (`succCover_zero`).  Along the levels
    `N_j = P ⊕ ω^{−1+a'}·j`, `j ≤ m`, all below `ω^{−1+a}` (`levelRoom`), `m` descents at the
    index `a'` (`chainTo`) carry `Acc_{N_m+1}(0)` (vacuous, `accZeroD`) down to
    `Acc_{P+1}(φ_{a'}^m(0))`.
  * `a` a limit: `x < φ_{a''}(0)` for some `1 ≤ a'' < a` (`limitCover_zero`); one descent at
    the index `a''` from the level `N + 1`, `N = ω^{−1+a''}`, carries `Acc_{N+1}(0)` to
    `Acc_N(φ_{a''}(0))`.

  In both cases the last step (`accSegD`) is a theorem of `RAlt (κ+1)`: the level-`κ` set
  `{y | y ≺₁ b̄ → X(y)}` is progressive when `X` is `≺`-progressive, so `Acc_κ(v̄)` gives
  `TI(≺, x̄, X)` for `x < v`; it is embedded and cut against `Acc_κ(v̄)`.  Every level used
  is below `ω^{−1+a}`, a limit level, so every cut rank `blkTop (L ⊕ 1)` is below
  `blk (ω^{−1+a})`; the rank depends on `x` (through `m`, or through `a''`), and only the
  existence of some rank below `blk (ω^{−1+a})` is uniform.  The height is below
  `hgtD a = ε₀ ⊕ ω^{a ⊕ 1}` for every `x`.

  ## The sharp lower half (`sf_lower_index`, `sf_lower_sharp`)

  A rank `ρ < ω^a`, `a > 1`, lies below `ω^{e ⊕ 1}` for `e = max(lead exponent of ρ, 1) < a`;
  predicative cut elimination leaves a cut-free derivation of height `φ_e^m(h)`, below
  `φ_a(0)` whenever `h < φ_a(0)`, since `φ_a(0)` is a fixed point of `φ_e`; boundedness then
  refutes `TI` along the segment below `φ_a(0)`.  At finite `γ` this is the statement of
  `sf_lower_omegaPow'` (`1 + n = n + 1`); at infinite `γ` that theorem is about the longer
  segment below `φ_{γ ⊕ 1}(0)`, and only the present form pairs with the upper half.

  ## The two-sided theorem (`sf_theorem`, `sf_theorem_epsilon_one`, `sf_theorem_ofNat`)

  The upper half uses cut ranks below `blk (ω^γ)` and heights below `hgtD (1+γ)`; the lower
  half excludes every cut rank below `blk (ω^γ)` together with every height below
  `φ_{1+γ}(0)`; and `hgtD (1+γ) < φ_{1+γ}(0)` (`hgtD_lt_veblenNote_zero`: `1 + γ < φ_{1+γ}(0)`
  below `Γ₀`, and `φ_{1+γ}(0)` is a fixed point of `ω^·` above `ε₀`).  So every derivation of
  the upper half lies in the region of the lower half, and the value `φ_{1+γ}(0)` is attained
  exactly.  For `γ < ε₁` (in particular `γ ≤ ε₀`) the heights of the upper half are below
  `ε₁`, and `ε₁ < φ_{1+γ}(0)`.  At `γ = n` the value is `φ_{n+1}(0)`.
-/
import OrdinalAnalysis.Ramified.DescentBeta

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open OrdinalAnalysis.Gamma0Note (veblenNote epsilonNote VeblenBelow)

/-! ### Ordinal arithmetic -/

section Notation

theorem lt_veblenNote_zero_self (a : Gamma0Note) : a < veblenNote a 0 := by
  rw [Gamma0Note.lt_def, Gamma0Note.repr_veblenNote, Gamma0Note.repr_zero]
  by_contra h
  exact absurd (Ordinal.gamma_zero_le_of_veblen_le (not_lt.mp h))
    (not_le.mpr (Gamma0Note.repr_lt_gamma_zero a))

theorem onePlusNote_predNote {a : Gamma0Note} (ha : (1 : Gamma0Note) ≤ a) :
    Gamma0Note.onePlusNote (Gamma0Note.predNote a) = a := by
  apply Gamma0Note.repr_injective
  rw [Gamma0Note.repr_onePlusNote, Gamma0Note.repr_predNote]
  have h1 : (1 : Ordinal) ≤ Gamma0Note.repr a := by
    rw [Gamma0Note.le_def, Gamma0Note.repr_one] at ha; exact ha
  exact Ordinal.add_sub_cancel_of_le h1

theorem one_lt_onePlusNote {γ : Gamma0Note} (hγ : (1 : Gamma0Note) ≤ γ) :
    (1 : Gamma0Note) < Gamma0Note.onePlusNote γ := by
  rw [Gamma0Note.lt_def, Gamma0Note.repr_onePlusNote, Gamma0Note.repr_one]
  rw [Gamma0Note.le_def, Gamma0Note.repr_one] at hγ
  exact lt_of_lt_of_le (lt_add_of_pos_right 1 zero_lt_one) (add_le_add_right hγ 1)

theorem onePlusNote_ofNat (n : ℕ) :
    Gamma0Note.onePlusNote (Gamma0Note.ofNat n) = Gamma0Note.ofNat (n + 1) := by
  apply Gamma0Note.repr_injective
  rw [Gamma0Note.repr_onePlusNote, Gamma0Note.repr_ofNat, Gamma0Note.repr_ofNat]
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.add_comm]

theorem predNote_ofNat_succ (n : ℕ) :
    Gamma0Note.predNote (Gamma0Note.ofNat (n + 1)) = Gamma0Note.ofNat n := by
  rw [← onePlusNote_ofNat, predNote_onePlusNote]

theorem epsilon_zero_lt_veblenNote_zero {a : Gamma0Note} (ha : (1 : Gamma0Note) < a) :
    epsilonNote 0 < veblenNote a 0 :=
  Gamma0Note.veblenNote_zero_lt_veblenNote_zero ha

/-- `ε₁ < φ_a(0)` for `a > 1`: `φ_a(0)` is a fixed point of `ε`. -/
theorem epsilon_one_lt_veblenNote_zero {a : Gamma0Note} (ha : (1 : Gamma0Note) < a) :
    epsilonNote 1 < veblenNote a 0 := by
  have hfix : veblenNote 1 (veblenNote a 0) = veblenNote a 0 :=
    Gamma0Note.veblenStructure.veblen_veblen_of_lt ha
  have h1 : (1 : Gamma0Note) < veblenNote a 0 :=
    lt_of_le_of_lt (le_of_lt ha) (lt_veblenNote_zero_self a)
  calc epsilonNote 1 = veblenNote 1 1 := rfl
    _ < veblenNote 1 (veblenNote a 0) := Gamma0Note.veblenNote_lt_veblenNote_right h1
    _ = veblenNote a 0 := hfix

/-- **The heights of `(D)` at the index `a > 1` stay below `φ_a(0)`.** -/
theorem hgtD_lt_veblenNote_zero {a : Gamma0Note} (ha : (1 : Gamma0Note) < a) :
    hgtD a < veblenNote a 0 :=
  hgtD_lt_of_fixed (Gamma0Note.omegaPow_veblenNote (le_of_lt ha) 0)
    (epsilon_zero_lt_veblenNote_zero ha) (lt_veblenNote_zero_self a)

/-- A rank below `ω^a`, `a > 1`, lies below `ω^{e ⊕ 1}` for some `1 ≤ e < a`. -/
theorem exists_index_of_lt_omegaPow {a ρ : Gamma0Note} (ha : (1 : Gamma0Note) < a)
    (hρ : ρ < Gamma0Note.omegaPow a) :
    ∃ e : Gamma0Note, (1 : Gamma0Note) ≤ e ∧ e < a ∧
      ρ < Gamma0Note.omegaPow (Gamma0Note.nadd e 1) := by
  have ha0 : (0 : Gamma0Note) < a := lt_trans Gamma0Note.zero_lt_one ha
  refine ⟨max (Gamma0Note.leadExpNote ρ) 1, le_max_right _ _,
    max_lt (Gamma0Note.leadExpNote_lt_of_lt_omegaPow ha0 hρ) ha, ?_⟩
  exact lt_of_lt_of_le (Gamma0Note.lt_omegaPow_leadExp_succ ρ)
    (Gamma0Note.omegaPow_le_omegaPow (Gamma0Note.nadd_le_nadd_left 1 (le_max_left _ _)))

end Notation

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)
open OrdinalAnalysis.Ramified.OmegaDerivableR (veblenIter veblenIter_lt_veblen)

/-! ### Transfinite induction up to a numeral, along a coded ordering -/

/-- **`TI(≺, ā, X) :≡ Prog(≺, X) → ∀y ≺ ā, X(y)`**, for a coded ordering `≺` given by
its defining formula; the bounded companion of `TIR prec = Prog(≺, X) → ∀y X(y)`. -/
def TIuptoR (prec : Semiformula LRA ℕ 2) (a : ℕ) : Proposition LRA :=
  ∼(Prog prec) ⋎
    (∀¹ (∼(precAt prec (#0 : Semiterm LRA ℕ 1) (numAtR a)) ⋎ Xat (#0 : Semiterm LRA ℕ 1)))

/-- The ordering of the segment below `φ_c(0)` is `precBelowR (φ_c(0))`. -/
theorem vebSegOrderR_prec_zero (c : Gamma0Note) (hc : 0 < c) :
    (vebSegOrderR c 0 hc).prec = precBelowR (veblenNote c 0) := rfl

/-- Along the segment below `b`, `TIuptoR` is the body of `tiUptoSegR b a`. -/
theorem TIuptoR_precBelowR (b a : Gamma0Note) :
    TIuptoR (precBelowR b) (gamma0Code a) = tiUptoSegBody b a := rfl

theorem univCl_TIuptoR_precBelowR (b a : Gamma0Note) :
    Semiformula.univCl (TIuptoR (precBelowR b) (gamma0Code a)) = tiUptoSegR b a := rfl

theorem freeVariables_precBelowR_eq_empty (b : Gamma0Note) : (precBelowR b).freeVariables = ∅ := by
  have h2 : (precAt precCode₁R (#1 : Semiterm LRA ℕ 2)
      (numAtR (gamma0Code b)) : Semiformula LRA ℕ 2).freeVariables = ∅ :=
    freeVariables_precAt_eq_empty precCode₁R freeVariables_precCode₁R (by simp)
      (freeVariables_of_groundR (groundR_numAtR _))
  simp [precBelowR, h2, freeVariables_precCode₁R]

theorem freeVariables_tiUptoSegBody (b a : Gamma0Note) :
    (tiUptoSegBody b a).freeVariables = ∅ := by
  have hp := freeVariables_precBelowR_eq_empty b
  have h1 := freeVariables_Prog (precBelowR b) hp
  have h2 : (precAt (precBelowR b) (#0 : Semiterm LRA ℕ 1)
      (numAtR (gamma0Code a))).freeVariables = ∅ :=
    freeVariables_precAt_eq_empty (precBelowR b) hp (by simp)
      (freeVariables_of_groundR (groundR_numAtR _))
  simp [tiUptoSegBody, h1, h2]

/-! ### The lower half at the Veblen index `a`, sharp -/

/-- **No derivation of cut rank below `ω^a` and height below `φ_a(0)` derives
transfinite induction along the segment below `φ_a(0)`**, `a > 1`, with the junk literals
among the axioms.  A rank `ρ < ω^a` lies below `ω^{e ⊕ 1}` for some `1 ≤ e < a`; cut
elimination leaves a cut-free derivation of height `φ_e^m(h)`, which is below `φ_a(0)`
since `φ_a(0)` is a fixed point of `φ_e`. -/
theorem sf_lower_index (a : Gamma0Note) (ha : (1 : Gamma0Note) < a) {ρ h : Gamma0Note}
    (hρ : ρ < Gamma0Note.omegaPow a) (hh : h < veblenNote a 0) :
    ¬ OmegaDerivableR junkLitsR evInstR ρ h
      [evR (TIR (vebSegOrderR a 0 (lt_trans Gamma0Note.zero_lt_one ha)).prec)] := by
  intro hder
  obtain ⟨e, he1, hea, hρe⟩ := exists_index_of_lt_omegaPow ha hρ
  obtain ⟨m, hd⟩ := cutFree_below_omegaPow_succ memFree_junkLitsR he1 hρe hder
  have hβ : veblenIter e m h < veblenNote a 0 := veblenIter_lt_veblen hea 0 m h hh
  have : OrdinalNotation (VeblenBelow a 0) :=
    Gamma0Note.VeblenBelow.ordinalNotation _ _ (lt_trans Gamma0Note.zero_lt_one ha)
  exact not_derivable_TI_R_junk _ (Below.mk _ hβ) (OmegaDerivableR.toBelow hd hβ)

/-- **The sharp lower half at the level `ω^γ`**, `γ ≥ 1`: no derivation of cut rank below
`blk (ω^γ) = ω^{1+γ}` and height below `φ_{1+γ}(0)` derives transfinite induction along the
segment below `φ_{1+γ}(0)`.  At finite `γ` this is `sf_lower_omegaPow'` (`1 + γ = γ ⊕ 1`);
at infinite `γ` the segment is shorter than there (`1 + γ = γ < γ ⊕ 1`) and matches the
upper half exactly. -/
theorem sf_lower_sharp (γ : Gamma0Note) (hγ : (1 : Gamma0Note) ≤ γ) {ρ h : Gamma0Note}
    (hρ : ρ < Gamma0Note.blk (Gamma0Note.omegaPow γ))
    (hh : h < veblenNote (Gamma0Note.onePlusNote γ) 0) :
    ¬ OmegaDerivableR junkLitsR evInstR ρ h
      [evR (TIR (vebSegOrderR (Gamma0Note.onePlusNote γ) 0
        (lt_trans Gamma0Note.zero_lt_one (one_lt_onePlusNote hγ))).prec)] :=
  sf_lower_index _ (one_lt_onePlusNote hγ) (by rwa [Gamma0Note.blk_omegaPow γ hγ] at hρ) hh

/-! ### The last step: from `Acc_κ(v)` to transfinite induction along a segment -/

section Model

variable {M : Type} [Nonempty M] [s : Structure LRA M] [Structure.Eq LRA M] {ν : Lv}

/-- In a model of `RAlt ν`: `TI_κ(v̄)` gives transfinite induction for `X` along `≺_b` up
to every `x < v`, `1 ≤ κ < ν`. -/
theorem accSeg_M (hM : M↓[LRA] ⊧* RAlt ν) {κ : Lv} (hκ : 1 ≤ κ) (hκν : κ < ν)
    {v x : Gamma0Note} (hxv : x < v) (b : Gamma0Note)
    (h : TImu κ (numVal M (gamma0Code v))) :
    (∀ x : M, (∀ y : M, precM y x ∧ precM x (numVal M (gamma0Code b)) → XM y) → XM x) →
      ∀ y : M, precM y (numVal M (gamma0Code x)) ∧
        precM (numVal M (gamma0Code x)) (numVal M (gamma0Code b)) → XM y := by
  have hν : 1 ≤ ν := le_trans hκ (le_of_lt hκν)
  have hκ0 : (0 : Gamma0Note) < κ := lt_of_lt_of_le Gamma0Note.zero_lt_one hκ
  set B : M := numVal M (gamma0Code b)
  have hshape : Shape κ (segGuardR b) :=
    shape_of_lvlOf_lt (by rw [lvlOf_segGuardR]; exact hκ0)
  obtain ⟨w, hw⟩ := comprM hM hκ0 hκν hshape (Classical.arbitrary M)
  have hG : ∀ y, memM κ y w ↔ (precM y B → XM y) := fun y =>
    (hw y).trans (eval_segGuardR _ y _)
  have hTI := (TIupM_congr hG _).mp (h w)
  intro hprog y hy
  have hprogG : ProgM (fun y : M => precM y B → XM y) := fun x hx hxB =>
    hprog x fun y hy' => hx y hy'.1 (precM_trans hM hν hy'.1 hxB)
  exact hTI hprogG y (precM_trans hM hν hy.1 (precM_code hM hν hxv)) (precM_trans hM hν hy.1 hy.2)

end Model

/-- **`RAlt (κ+1) ⊢ TI_κ(v̄) → TI(≺_b, x̄, X)`** for notations `x < v`, `κ ≥ 1`. -/
theorem accSeg_provable {κ : Lv} (hκ : 1 ≤ κ) {v x : Gamma0Note} (hxv : x < v) (b : Gamma0Note) :
    RAlt (Gamma0Note.nadd κ 1) ⊢
      Semiformula.univCl (∼accA κ (gamma0Code v) ⋎ tiUptoSegBody b x) := by
  have hν : 1 ≤ Gamma0Note.nadd κ 1 := Gamma0Note.one_le_nadd_one κ
  refine provable_of_eqModels hν ?_ ?_
  · rw [lvlOf_emb_univCl, lvlOf_or, lvlOf_neg, lvlOf_tiUptoSegBody]
    exact max_lt (lt_of_le_of_lt (lvlOf_accA_le κ _) (Gamma0Note.lt_nadd_one κ))
      (lt_of_lt_of_le Gamma0Note.zero_lt_one hν)
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f (∼accA κ (gamma0Code v) ⋎ tiUptoSegBody b x)
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, eval_accA,
      tiUptoSegBody, eval_tiUptoSegR_body]
    by_cases h : TImu κ (numVal N (gamma0Code v))
    · exact Or.inr (accSeg_M hN hκ (Gamma0Note.lt_nadd_one κ) hxv b h)
    · exact Or.inl h

/-- **The last step, embedded**: `¬Acc_κ(v̄), TI(≺_b, x̄, X)` for `x < v`, `κ ≥ 1`, at any
cut rank from `blkTop (κ ⊕ 1)` on, below `ε₀`. -/
theorem accSegD {κ : Lv} (hκ : 1 ≤ κ) {v x : Gamma0Note} (hxv : x < v) (b : Gamma0Note)
    {ρ : Gamma0Note} (hρ : Gamma0Note.blkTop (Gamma0Note.nadd κ 1) ≤ ρ) {H : Gamma0Note}
    (hH : epsilonNote 0 ≤ H) :
    DerLt ρ [evR (∼accA κ (gamma0Code v)), evR (tiUptoSegBody b x)] H := by
  have h := DerLt.of_RAlt (Gamma0Note.one_le_nadd_one κ)
    (by rw [Semiformula.freeVariables_or, Semiformula.freeVariables_not, freeVariables_accA,
      freeVariables_tiUptoSegBody, Finset.union_empty])
    (accSeg_provable hκ hxv b) hρ hH
  rw [evR_or] at h
  exact h.invOr

/-! ### A chain of descents with room up to its length only -/

/-- **`m` applications of `(D)` at the index `a'`**, along the levels
`N_j = P ⊕ ω^{−1+a'}·j`, `j ≤ m`, inside a level `L ≥ N_m ⊕ 1`:
`¬Acc_{N_m+1}(ȳ), Acc_{P+1}(φ_{a'}^m(y)‾)` at cut rank `blkTop (L ⊕ 1)`, below
`hgtD a' ⊕ (2m + 1)`.  Unlike `chain`, only the levels actually used need room below `L`,
so `L` itself can be taken right above `N_m`. -/
theorem chainTo {a' : Gamma0Note}
    (IH : ∀ N : Lv, EndsIn (Gamma0Note.predNote a') N → DescentAt a' N)
    {P : Lv} (hP : Gamma0Note.PowClosed (Gamma0Note.predNote a') P) :
    ∀ (m : ℕ) (y : Gamma0Note) {L : Lv}, Gamma0Note.nadd (Gamma0Note.nadd P
      (Gamma0Note.omegaPowMul (Gamma0Note.predNote a') m)) 1 ≤ L →
      DerLt (Gamma0Note.blkTop (Gamma0Note.nadd L 1))
        [evR (∼accA (Gamma0Note.nadd (Gamma0Note.nadd P
            (Gamma0Note.omegaPowMul (Gamma0Note.predNote a') m)) 1) (gamma0Code y)),
          evR (accA (Gamma0Note.nadd P 1) (gamma0Code (Gamma0Note.phiIter a' m y)))]
        (Gamma0Note.nadd (hgtD a') (Gamma0Note.ofNat (2 * m + 1)))
  | 0, y, L, hL => by
      have e0 : Gamma0Note.nadd P (Gamma0Note.omegaPowMul (Gamma0Note.predNote a') 0) = P := by
        rw [Gamma0Note.omegaPowMul_zero, Gamma0Note.nadd_zero]
      rw [e0] at hL ⊢
      exact copyD le_rfl (gamma0Code y) (blkTop_le_of_le hL) (eps_le_hgtD_nadd a' _)
  | (m + 1), y, L, hL => by
      set e' := Gamma0Note.predNote a' with he'
      have hNL : Gamma0Note.nadd P (Gamma0Note.omegaPowMul e' (m + 1)) ≤ L :=
        le_trans (le_of_lt (Gamma0Note.lt_nadd_one _)) hL
      have hN1L : Gamma0Note.nadd (Gamma0Note.nadd P (Gamma0Note.omegaPowMul e' m)) 1 ≤ L :=
        le_trans (nadd_omegaPowMul_succ_le hP m) hNL
      have hD := (IH _ (endsIn_chain hP m) y).mono_rank (blkTop_le_of_le hNL)
      have hC := copyD (ρ := Gamma0Note.blkTop (Gamma0Note.nadd L 1))
        (nadd_omegaPowMul_succ_le hP m) (gamma0Code (Gamma0Note.veblenNote a' y))
        (blkTop_le_of_le hNL) (eps_le_hgtD a')
      have T1 := transfer (Γ := [evR (∼accA (Gamma0Note.nadd (Gamma0Note.nadd P
          (Gamma0Note.omegaPowMul e' (m + 1))) 1) (gamma0Code y))])
        (rank_accA_lt hNL _) hC (hD.weak (by subset_tac))
        (lt_nadd_ofNat_one (hgtD a'))
      have R := chainTo IH hP m (Gamma0Note.veblenNote a' y) hN1L
      have T2 := transfer (rank_accA_lt hN1L _) R
        (T1.mono (nadd_ofNat_le_nadd_ofNat _ (by omega)))
        (nadd_ofNat_lt_nadd_ofNat (hgtD a') (Nat.lt_succ_self (2 * m + 1)))
      have hit : Gamma0Note.phiIter a' (m + 1) y =
          Gamma0Note.phiIter a' m (Gamma0Note.veblenNote a' y) :=
        Function.iterate_succ_apply _ m y
      rw [hit]
      exact (T2.weak (by subset_tac)).mono (nadd_ofNat_le_nadd_ofNat _ (by omega))

/-! ### The upper half at the Veblen index `a` -/

/-- Cut `Acc_κ(v̄)` against the last step. -/
theorem finishSeg {κ L : Lv} (hκ : 1 ≤ κ) (hκL : κ ≤ L) {v x : Gamma0Note} (hxv : x < v)
    (b : Gamma0Note) {H : Gamma0Note} (hH : epsilonNote 0 ≤ H)
    (hA : DerLt (Gamma0Note.blkTop (Gamma0Note.nadd L 1)) [evR (accA κ (gamma0Code v))] H) :
    DerLt (Gamma0Note.blkTop (Gamma0Note.nadd L 1)) [evR (tiUptoSegBody b x)]
      (Gamma0Note.nadd H (Gamma0Note.ofNat 1)) := by
  have fs := accSegD hκ hxv b (blkTop_le_of_le hκL) hH
  rw [evR_neg] at fs
  have t := DerLt.cutHyp (by rw [rank_evR]; exact rank_accA_lt hκL _) fs hA
    (lt_nadd_ofNat_one H)
  exact t.weak (by subset_tac)

/-- **The upper half at a successor index `a' ⊕ 1`**, `a' ≥ 1`: for every
`x < φ_{a'⊕1}(0)`, `TI(≺_{φ_{a'⊕1}(0)}, x̄, X)` is derivable at a cut rank below
`blk (ω^{−1+(a'⊕1)})` and below the height `hgtD (a' ⊕ 1)`.  From `Acc(0)` at the top of a
chain of `m` descents at the index `a'`, `x < φ_{a'}^m(0)`. -/
theorem upper_succ {a' : Gamma0Note} (ha' : (1 : Gamma0Note) ≤ a') {x : Gamma0Note}
    (hx : x < veblenNote (Gamma0Note.nadd a' 1) 0) :
    ∃ ρ : Gamma0Note, ρ < Gamma0Note.blk
        (Gamma0Note.omegaPow (Gamma0Note.predNote (Gamma0Note.nadd a' 1))) ∧
      DerLt ρ [evR (tiUptoSegBody (veblenNote (Gamma0Note.nadd a' 1) 0) x)]
        (hgtD (Gamma0Note.nadd a' 1)) := by
  rw [predNote_nadd_one ha']
  set e' := Gamma0Note.predNote a' with he'
  set E := epsilonNote 0 with hE
  have hΛ1 : (1 : Gamma0Note) ≤ Gamma0Note.nadd e' 1 := Gamma0Note.one_le_nadd_one e'
  obtain ⟨P, hP, -, hroom⟩ := levelRoom (Gamma0Note.lt_nadd_one e')
    (Gamma0Note.powClosed_zero (Gamma0Note.nadd e' 1)) (κ := 0)
    (by rw [Gamma0Note.zero_nadd]; exact Gamma0Note.omegaPow_pos _)
  obtain ⟨m, hm⟩ := Gamma0Note.succCover_zero hx
  set L := Gamma0Note.nadd (Gamma0Note.nadd P (Gamma0Note.omegaPowMul e' m)) 1 with hLdef
  have hLΛ : L < Gamma0Note.omegaPow (Gamma0Note.nadd e' 1) := by
    have h := hroom m
    rwa [Gamma0Note.zero_nadd] at h
  set ρL := Gamma0Note.blkTop (Gamma0Note.nadd L 1) with hρL
  have hρ1 : Gamma0Note.omegaPow 1 ≤ ρL := omegaPow_one_le_blkTop (nadd_one_ne_zero L)
  refine ⟨ρL, Gamma0Note.blkTop_lt_blk_of_limit (Gamma0Note.omegaPow_limit hΛ1)
    (Gamma0Note.omegaPow_limit hΛ1 L hLΛ), ?_⟩
  have hch := chainTo (descentAt_all a' ha') hP m 0 (le_refl L)
  have h0 := accZeroD (ρ := ρL) (μ := L) hρ1 le_rfl (Γ := []) (le_refl E)
  have t1 := transfer (rank_accA_lt (le_refl L) _) hch
    (h0.mono (eps_nadd_le_hgtD_nadd a' 6 (2 * m + 1)))
    (nadd_ofNat_lt_nadd_ofNat (hgtD a') (Nat.lt_succ_self (2 * m + 1)))
  have hP1L : Gamma0Note.nadd P 1 ≤ L :=
    Gamma0Note.nadd_le_nadd_left 1 (Gamma0Note.le_nadd_left _ _)
  have fin := finishSeg (Gamma0Note.one_le_nadd_one P) hP1L hm
    (veblenNote (Gamma0Note.nadd a' 1) 0) (eps_le_hgtD_nadd a' (2 * m + 2)) t1
  rw [nadd_ofNat_add] at fin
  refine fin.mono (le_of_lt (lt_of_lt_of_le (hgtD_nadd_lt_bndD_succ a' _) ?_))
  exact le_of_lt (lt_of_le_of_lt (le_nadd_ofNat _ 0)
    (bndD_nadd_lt_hgtD (Gamma0Note.one_le_nadd_one a') 0))

/-- **The upper half at a limit index `a`**: for every `x < φ_a(0)`,
`TI(≺_{φ_a(0)}, x̄, X)` is derivable at a cut rank below `blk (ω^a)` and below the height
`hgtD a`.  From `Acc(0)` and one descent at an index `a'' < a` with `x < φ_{a''}(0)`. -/
theorem upper_limit {a : Gamma0Note} (ha : Order.IsSuccLimit (Gamma0Note.repr a))
    {x : Gamma0Note} (hx : x < veblenNote a 0) :
    ∃ ρ : Gamma0Note, ρ < Gamma0Note.blk (Gamma0Note.omegaPow (Gamma0Note.predNote a)) ∧
      DerLt ρ [evR (tiUptoSegBody (veblenNote a 0) x)] (hgtD a) := by
  rw [predNote_of_limit ha]
  set E := epsilonNote 0 with hE
  have h1a : (1 : Gamma0Note) < a := one_lt_of_limit ha
  obtain ⟨β'', hβ, hxβ⟩ := Gamma0Note.limitCover_zero ha hx
  set a'' := max β'' 1 with ha''def
  have ha''a : a'' < a := max_lt hβ h1a
  have ha''1 : (1 : Gamma0Note) ≤ a'' := le_max_right _ _
  have hx' : x < veblenNote a'' 0 :=
    lt_of_lt_of_le hxβ (Gamma0Note.veblenNote_le_veblenNote_left (le_max_left _ _))
  set N := Gamma0Note.omegaPow (Gamma0Note.predNote a'') with hNdef
  have hNe : EndsIn (Gamma0Note.predNote a'') N :=
    ⟨0, Gamma0Note.powClosed_zero _, (Gamma0Note.zero_nadd _).symm⟩
  have hNa : N < Gamma0Note.omegaPow a :=
    Gamma0Note.omegaPow_lt_omegaPow (lt_of_le_of_lt (predNote_le a'') ha''a)
  have ha1 : (1 : Gamma0Note) ≤ a := le_of_lt h1a
  have hN1 : Gamma0Note.nadd N 1 < Gamma0Note.omegaPow a := Gamma0Note.omegaPow_limit ha1 N hNa
  set N1 := Gamma0Note.nadd N 1 with hN1def
  set ρL := Gamma0Note.blkTop (Gamma0Note.nadd N1 1) with hρL
  have hρ1 : Gamma0Note.omegaPow 1 ≤ ρL := omegaPow_one_le_blkTop (nadd_one_ne_zero N1)
  refine ⟨ρL, Gamma0Note.blkTop_lt_blk_of_limit (Gamma0Note.omegaPow_limit ha1)
    (Gamma0Note.omegaPow_limit ha1 N1 hN1), ?_⟩
  have hNN1 : N ≤ N1 := le_of_lt (Gamma0Note.lt_nadd_one N)
  have hD := (descentAt_all a'' ha''1 N hNe 0).mono_rank (blkTop_le_of_le hNN1)
  have h0 := accZeroD (ρ := ρL) (μ := N1) hρ1 le_rfl (Γ := []) (le_refl E)
  have t1 := transfer (rank_accA_lt (le_refl N1) _) hD (h0.mono (eps_nadd_le_hgtD a'' 6))
    (lt_nadd_ofNat_one (hgtD a''))
  have fin := finishSeg (Gamma0Note.one_le_omegaPow _) hNN1 hx' (veblenNote a 0)
    (eps_le_hgtD_nadd a'' 1) t1
  rw [nadd_ofNat_add] at fin
  refine fin.mono (le_of_lt (lt_of_lt_of_le
    (hgtD_nadd_lt_bndD_of_lt (nadd_one_lt_of_limit ha ha''a) _) ?_))
  exact le_of_lt (lt_of_le_of_lt (le_nadd_ofNat _ 0) (bndD_nadd_lt_hgtD ha1 0))

/-- **The upper half at the Veblen index `a > 1`**: for every `x < φ_a(0)`, transfinite
induction along the segment below `φ_a(0)` up to `x̄` is derivable at a cut rank below
`blk (ω^{−1+a})` and below the height `hgtD a`. -/
theorem upper_index (a : Gamma0Note) (ha : (1 : Gamma0Note) < a) {x : Gamma0Note}
    (hx : x < veblenNote a 0) :
    ∃ ρ : Gamma0Note, ρ < Gamma0Note.blk (Gamma0Note.omegaPow (Gamma0Note.predNote a)) ∧
      DerLt ρ [evR (tiUptoSegBody (veblenNote a 0) x)] (hgtD a) := by
  rcases Gamma0Note.zero_or_exists_pred_or_isSuccLimit a with rfl | ⟨a', rfl⟩ | hlim
  · exact absurd (lt_trans Gamma0Note.zero_lt_one ha) (lt_irrefl _)
  · have ha' : (1 : Gamma0Note) ≤ a' := by
      by_contra h
      have h' : Gamma0Note.nadd a' 1 ≤ 1 := Gamma0Note.nadd_one_le_of_lt (lt_of_not_ge h)
      exact absurd ha (not_lt.mpr h')
    exact upper_succ ha' hx
  · exact upper_limit hlim hx

/-! ### Both halves at the Veblen index `a` -/

theorem one_le_predNote_of_one_lt {a : Gamma0Note} (ha : (1 : Gamma0Note) < a) :
    (1 : Gamma0Note) ≤ Gamma0Note.predNote a := by
  rw [Gamma0Note.le_def, Gamma0Note.repr_predNote, Gamma0Note.repr_one]
  rw [Gamma0Note.lt_def, Gamma0Note.repr_one] at ha
  exact Ordinal.le_sub_of_add_le (Order.add_one_le_of_lt ha)

/-- `blk (ω^{−1+a}) = ω^a`, `a > 1`. -/
theorem blk_omegaPow_predNote {a : Gamma0Note} (ha : (1 : Gamma0Note) < a) :
    Gamma0Note.blk (Gamma0Note.omegaPow (Gamma0Note.predNote a)) = Gamma0Note.omegaPow a := by
  rw [Gamma0Note.blk_omegaPow _ (one_le_predNote_of_one_lt ha),
    onePlusNote_predNote (le_of_lt ha)]

/-- **Both halves at the Veblen index `a > 1`, level `ω^{−1+a}`, value `φ_a(0)`.**

* Upper: for every `x < φ_a(0)`, transfinite induction along the segment below `φ_a(0)` up
  to `x̄` is derivable at some cut rank below `blk (ω^{−1+a})` and some height below
  `hgtD a`.
* Lower: transfinite induction along the whole segment is derivable at no cut rank below
  `blk (ω^{−1+a})` and no height below `φ_a(0)`.
* The heights of the upper half lie in the region of the lower half: `hgtD a < φ_a(0)`. -/
theorem sf_theorem_index (a : Gamma0Note) (ha : (1 : Gamma0Note) < a) :
    (∀ x : Gamma0Note, x < veblenNote a 0 →
      ∃ ρ h : Gamma0Note,
        ρ < Gamma0Note.blk (Gamma0Note.omegaPow (Gamma0Note.predNote a)) ∧ h < hgtD a ∧
        OmegaDerivableR junkLitsR evInstR ρ h
          [evR (TIuptoR (vebSegOrderR a 0 (lt_trans Gamma0Note.zero_lt_one ha)).prec
            (gamma0Code x))]) ∧
    (∀ ρ h : Gamma0Note,
      ρ < Gamma0Note.blk (Gamma0Note.omegaPow (Gamma0Note.predNote a)) →
      h < veblenNote a 0 →
        ¬ OmegaDerivableR junkLitsR evInstR ρ h
          [evR (TIR (vebSegOrderR a 0 (lt_trans Gamma0Note.zero_lt_one ha)).prec)]) ∧
    hgtD a < veblenNote a 0 := by
  refine ⟨fun x hx => ?_, fun ρ h hρ hh => ?_, hgtD_lt_veblenNote_zero ha⟩
  · obtain ⟨ρ, hρ, α, hα, d⟩ := upper_index a ha hx
    exact ⟨ρ, α, hρ, hα, d⟩
  · rw [blk_omegaPow_predNote ha] at hρ
    exact sf_lower_index a ha hρ hh

/-! ### The headlines at the level `ω^γ` -/

/-- **The upper half at the level `ω^γ`**, `γ ≥ 1`: for every `x < φ_{1+γ}(0)` there is a
derivation of `TI(≺_{φ_{1+γ}(0)}, x̄, X)` in `RA_∞` with the junk literals, of cut rank below
`blk (ω^γ) = ω^{1+γ}` and height below `hgtD (1+γ) = ε₀ ⊕ ω^{(1+γ) ⊕ 1}`. -/
theorem sf_upper (γ : Gamma0Note) (hγ : (1 : Gamma0Note) ≤ γ) {x : Gamma0Note}
    (hx : x < veblenNote (Gamma0Note.onePlusNote γ) 0) :
    ∃ ρ h : Gamma0Note, ρ < Gamma0Note.blk (Gamma0Note.omegaPow γ) ∧
      h < hgtD (Gamma0Note.onePlusNote γ) ∧
      OmegaDerivableR junkLitsR evInstR ρ h
        [evR (TIuptoR (vebSegOrderR (Gamma0Note.onePlusNote γ) 0
          (lt_trans Gamma0Note.zero_lt_one (one_lt_onePlusNote hγ))).prec (gamma0Code x))] := by
  have h := (sf_theorem_index _ (one_lt_onePlusNote hγ)).1 x hx
  rwa [predNote_onePlusNote] at h

/-- `1 + γ < ε₁` for `γ < ε₁`. -/
theorem onePlusNote_lt_epsilon_one {γ : Gamma0Note} (hγ : γ < epsilonNote 1) :
    Gamma0Note.onePlusNote γ < epsilonNote 1 := by
  have h1 : (1 : Gamma0Note) < epsilonNote 1 :=
    lt_of_lt_of_le (by rw [← Gamma0Note.ofNat_one]; exact ofNat_lt_epsilonNote_zero 1)
      (Gamma0Note.epsilon_le_epsilon (Gamma0Note.zero_le_note 1))
  exact lt_of_le_of_lt (Gamma0Note.onePlusNote_le_nadd_one γ) (Gamma0Note.nadd_lt_epsilon hγ h1)

/-- **The upper half at the level `ω^γ`, heights below `ε₁`**, for `1 ≤ γ < ε₁` (in
particular for every `1 ≤ γ ≤ ε₀`). -/
theorem sf_upper_epsilon_one (γ : Gamma0Note) (hγ : (1 : Gamma0Note) ≤ γ)
    (hγε : γ < epsilonNote 1) {x : Gamma0Note}
    (hx : x < veblenNote (Gamma0Note.onePlusNote γ) 0) :
    ∃ ρ h : Gamma0Note, ρ < Gamma0Note.blk (Gamma0Note.omegaPow γ) ∧ h < epsilonNote 1 ∧
      OmegaDerivableR junkLitsR evInstR ρ h
        [evR (TIuptoR (vebSegOrderR (Gamma0Note.onePlusNote γ) 0
          (lt_trans Gamma0Note.zero_lt_one (one_lt_onePlusNote hγ))).prec (gamma0Code x))] := by
  obtain ⟨ρ, h, hρ, hh, d⟩ := sf_upper γ hγ hx
  exact ⟨ρ, h, hρ, lt_trans hh (hgtD_lt_epsilon Gamma0Note.zero_lt_one
    (onePlusNote_lt_epsilon_one hγε)), d⟩

/-- **The semiformal analysis at the level `ω^γ`, both halves, sharp**, `γ ≥ 1`, value
`φ_{1+γ}(0)` (`1 + γ` genuine ordinal addition: `φ_{n+1}(0)` at `γ = n`, `φ_γ(0)` at
`γ ≥ ω`), along the segment ordering `≺` below `φ_{1+γ}(0)`, in `RA_∞` with the junk
literals:

* (upper) for every `x < φ_{1+γ}(0)`, `Prog(≺, X) → ∀y ≺ x̄, X(y)` is derivable at some cut
  rank below `blk (ω^γ)` and some height below `hgtD (1+γ) = ε₀ ⊕ ω^{(1+γ) ⊕ 1}`;
* (lower) `Prog(≺, X) → ∀y X(y)` is derivable at no cut rank below `blk (ω^γ)` and no height
  below `φ_{1+γ}(0)`;
* (matching) `hgtD (1+γ) < φ_{1+γ}(0)`: the derivations of the upper half have cut rank and
  height inside the region excluded by the lower half. -/
theorem sf_theorem (γ : Gamma0Note) (hγ : (1 : Gamma0Note) ≤ γ) :
    (∀ x : Gamma0Note, x < veblenNote (Gamma0Note.onePlusNote γ) 0 →
      ∃ ρ h : Gamma0Note, ρ < Gamma0Note.blk (Gamma0Note.omegaPow γ) ∧
        h < hgtD (Gamma0Note.onePlusNote γ) ∧
        OmegaDerivableR junkLitsR evInstR ρ h
          [evR (TIuptoR (vebSegOrderR (Gamma0Note.onePlusNote γ) 0
            (lt_trans Gamma0Note.zero_lt_one (one_lt_onePlusNote hγ))).prec (gamma0Code x))]) ∧
    (∀ ρ h : Gamma0Note, ρ < Gamma0Note.blk (Gamma0Note.omegaPow γ) →
      h < veblenNote (Gamma0Note.onePlusNote γ) 0 →
        ¬ OmegaDerivableR junkLitsR evInstR ρ h
          [evR (TIR (vebSegOrderR (Gamma0Note.onePlusNote γ) 0
            (lt_trans Gamma0Note.zero_lt_one (one_lt_onePlusNote hγ))).prec)]) ∧
    hgtD (Gamma0Note.onePlusNote γ) < veblenNote (Gamma0Note.onePlusNote γ) 0 :=
  ⟨fun _ hx => sf_upper γ hγ hx, fun _ _ hρ hh => sf_lower_sharp γ hγ hρ hh,
    hgtD_lt_veblenNote_zero (one_lt_onePlusNote hγ)⟩

/-- **`sf_theorem` with the height bound `ε₁`**, for `1 ≤ γ < ε₁`: the upper half at heights
below `ε₁`, the lower half at every height below `φ_{1+γ}(0)`, and `ε₁ < φ_{1+γ}(0)`. -/
theorem sf_theorem_epsilon_one (γ : Gamma0Note) (hγ : (1 : Gamma0Note) ≤ γ)
    (hγε : γ < epsilonNote 1) :
    (∀ x : Gamma0Note, x < veblenNote (Gamma0Note.onePlusNote γ) 0 →
      ∃ ρ h : Gamma0Note, ρ < Gamma0Note.blk (Gamma0Note.omegaPow γ) ∧ h < epsilonNote 1 ∧
        OmegaDerivableR junkLitsR evInstR ρ h
          [evR (TIuptoR (vebSegOrderR (Gamma0Note.onePlusNote γ) 0
            (lt_trans Gamma0Note.zero_lt_one (one_lt_onePlusNote hγ))).prec (gamma0Code x))]) ∧
    (∀ ρ h : Gamma0Note, ρ < Gamma0Note.blk (Gamma0Note.omegaPow γ) →
      h < veblenNote (Gamma0Note.onePlusNote γ) 0 →
        ¬ OmegaDerivableR junkLitsR evInstR ρ h
          [evR (TIR (vebSegOrderR (Gamma0Note.onePlusNote γ) 0
            (lt_trans Gamma0Note.zero_lt_one (one_lt_onePlusNote hγ))).prec)]) ∧
    epsilonNote 1 < veblenNote (Gamma0Note.onePlusNote γ) 0 :=
  ⟨fun _ hx => sf_upper_epsilon_one γ hγ hγε hx, fun _ _ hρ hh => sf_lower_sharp γ hγ hρ hh,
    epsilon_one_lt_veblenNote_zero (one_lt_onePlusNote hγ)⟩

theorem one_lt_ofNat_succ {n : ℕ} (hn : 1 ≤ n) : (1 : Gamma0Note) < Gamma0Note.ofNat (n + 1) := by
  rw [← Gamma0Note.ofNat_one]
  exact Gamma0Note.ofNat_lt_ofNat (by omega)

/-- **`sf_theorem` at a finite level `ω^n`**, `n ≥ 1`: value `φ_{n+1}(0)`, cut ranks below
`blk (ω^n) = ω^{n+1}`, heights of the upper half below `hgtD (n+1) = ε₀ ⊕ ω^{n+2}`
(`1 + n = n + 1`, `onePlusNote_ofNat`). -/
theorem sf_theorem_ofNat {n : ℕ} (hn : 1 ≤ n) :
    (∀ x : Gamma0Note, x < veblenNote (Gamma0Note.ofNat (n + 1)) 0 →
      ∃ ρ h : Gamma0Note, ρ < Gamma0Note.blk (Gamma0Note.omegaPow (Gamma0Note.ofNat n)) ∧
        h < hgtD (Gamma0Note.ofNat (n + 1)) ∧
        OmegaDerivableR junkLitsR evInstR ρ h
          [evR (TIuptoR (vebSegOrderR (Gamma0Note.ofNat (n + 1)) 0
            (lt_trans Gamma0Note.zero_lt_one (one_lt_ofNat_succ hn))).prec (gamma0Code x))]) ∧
    (∀ ρ h : Gamma0Note, ρ < Gamma0Note.blk (Gamma0Note.omegaPow (Gamma0Note.ofNat n)) →
      h < veblenNote (Gamma0Note.ofNat (n + 1)) 0 →
        ¬ OmegaDerivableR junkLitsR evInstR ρ h
          [evR (TIR (vebSegOrderR (Gamma0Note.ofNat (n + 1)) 0
            (lt_trans Gamma0Note.zero_lt_one (one_lt_ofNat_succ hn))).prec)]) ∧
    hgtD (Gamma0Note.ofNat (n + 1)) < veblenNote (Gamma0Note.ofNat (n + 1)) 0 := by
  have h := sf_theorem_index _ (one_lt_ofNat_succ hn)
  rw [predNote_ofNat_succ] at h
  exact h

/-! ### Axiom audit -/

#print axioms lt_veblenNote_zero_self
#print axioms sf_lower_index
#print axioms sf_lower_sharp
#print axioms accSeg_provable
#print axioms accSegD
#print axioms chainTo
#print axioms upper_succ
#print axioms upper_limit
#print axioms upper_index
#print axioms sf_theorem_index
#print axioms sf_upper
#print axioms sf_upper_epsilon_one
#print axioms sf_theorem
#print axioms sf_theorem_epsilon_one
#print axioms sf_theorem_ofNat

end Ramified

end OrdinalAnalysis
