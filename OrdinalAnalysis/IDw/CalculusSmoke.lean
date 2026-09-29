/-
  Smoke tests for `IDw.Calculus` (design `idomega_design.md` §3.2, stage C1): the two new rules
  `jlev`/`njlev` exercised together with `fix`, `orR`, `all`, `literal`, in the uniform theory
  with the trivial form `A := ⊤` (so every level `I_k` is all of `ℕ`, and `fix` at level `k`
  needs only `Ω_{k+1} ⪯ α` and the trivial premise `⊤`).

    `jlevTop_derivable`      `Jlev ⊤ (m̄, t) ∈ Γ` is derivable at `β + 1` once `Ω_{m+1} ⪯ β`
                             (rule `jlev` at level `m`, then rule `fix` at level `m`)
    `smoke_jlev_zero`        `⊢ Jlev ⊤ (0̄, 0̄)` at height `Ω_1 + 1` (jlev + fix₀)
    `smoke_jlev_lt_two`      `⊢ ∀y (y < 2 → Jlev ⊤ (y, 0̄))` at height `Ω_2 + 3 ≺ Ω_3`
    `smoke_jlev_all`         `⊢ ∀y Jlev ⊤ (y, y)` at height `Ω_ω` (the ω-rule over every level)
    `smoke_njlev_empty`      `⊢ ¬Jlev 1 (1̄, 0̄)`: an empty conjunction, height `0`
    `smoke_njlev_prem`       `⊢ ¬Jlev 1 (0̄, 0̄), Jlev ⊤ (0̄, 0̄)`: `njlev` with its premise

  (The design's third test `∀y Jlev ⊤ (y, code(Ω_y))` cannot be written in `LIinfW` as stated:
  `ℒₒᵣ` has no function symbol `y ↦ code(Ω_y)`; see the notes.  `Jlev ⊤ (y, y)` has the same
  derivation shape, `f m = Ω_{m+1} + 1` unbounded below `Ω_ω`.)
-/
import OrdinalAnalysis.IDw.Calculus

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder

/-! ### Setting: the trivial operator and the trivial form -/

/-- The trivial operator: every control condition holds for free. -/
def Htriv : Set ThetaVNoteD → Set ThetaVNoteD := fun _ => Set.univ

theorem Htriv_isOperator : ThetaVNoteD.IsOperator Htriv :=
  ⟨fun _ => Set.subset_univ _, fun _ _ _ => Set.subset_univ _⟩

/-- The trivial form `A := ⊤`: `I_k` is everything, at every level. -/
def smokeA : FormJ := ⊤

theorem unfoldW_smokeA {ξ : Type*} {m : ℕ} (k : ℕ) (g : StageAt k) (t : Semiterm LIinfW ξ m) :
    unfoldW smokeA k g t = ⊤ := by
  simp [unfoldW, formAtW, smokeA]

/-! ### Ordinal facts (`ThetaVNoteD` has no order tactic yet) -/

theorem zero_lt_Omega (k : ℕ) : ThetaVNoteD.zero < ThetaVNoteD.Omega k := by
  have := ThetaVNoteD.ofNat_lt_prin (p := ThetaVNoteD.Omega k) (ThetaVTerm.isPrin_Omega k) 0
  rwa [ThetaVNoteD.ofNat_zero] at this

theorem Omega_lt_Omega {i j : ℕ} (h : i < j) : ThetaVNoteD.Omega i < ThetaVNoteD.Omega j :=
  ThetaVNoteD.lt_iff.mpr ((ThetaVTerm.Omega_lt_Omega_iff i j).mpr h)

theorem one_lt_Omega (k : ℕ) : ThetaVNoteD.one < ThetaVNoteD.Omega k :=
  ThetaVNoteD.one_lt_prin (ThetaVTerm.isPrin_Omega k)

theorem succ_lt_Omega {x : ThetaVNoteD} {k : ℕ} (h : x < ThetaVNoteD.Omega k) :
    ThetaVNoteD.succ x < ThetaVNoteD.Omega k :=
  ThetaVNoteD.succ_lt_prin (ThetaVTerm.isPrin_Omega k) h

theorem succ_lt_OmegaW {x : ThetaVNoteD} (h : x < ThetaVNoteD.OmegaW) :
    ThetaVNoteD.succ x < ThetaVNoteD.OmegaW :=
  ThetaVNoteD.succ_lt_prin (ThetaVTerm.isPrin_OmegaW) h

/-! ### `fix` and `jlev` at the trivial form -/

/-- `fix` at level `k` for the trivial form: `I_k t ∈ Γ` is derivable at `Ω_{k+1}`. -/
theorem fix_smoke (k : ℕ) (t : SyntacticTerm LIinfW) (Γ : Sequent LIinfW)
    (hm : IOmegaAt k t ∈ Γ) :
    IDwDerivable smokeA ThetaVNoteD.zero Htriv (ThetaVNoteD.Omega k) Γ := by
  refine .fix (Set.mem_univ _) (Set.subset_univ _) hm (le_refl _) (zero_lt_Omega k) ?_
  rw [unfoldW_smokeA]
  exact .verum (Set.mem_univ _) (Set.subset_univ _) List.mem_cons_self

/-- **`jlev` then `fix`**: `Jlev ⊤ (m̄, t) ∈ Γ` for closed `t` is derivable at `β + 1` whenever
`Ω_{m+1} ⪯ β`. -/
theorem jlevTop_derivable (m : ℕ) (t : SyntacticTerm LIinfW) (Γ : Sequent LIinfW)
    (ht : t.freeVariables = ∅) (hm : jlevAt ⊤ (numI m) t ∈ Γ) {β : ThetaVNoteD}
    (hβ : ThetaVNoteD.Omega m ≤ β) :
    IDwDerivable smokeA ThetaVNoteD.zero Htriv (ThetaVNoteD.succ β) Γ := by
  refine .jlev (Set.mem_univ _) (Set.subset_univ _) hm (numI_freeVariables m) ht
    (by rw [termVal_numI]; exact WithTop.coe_lt_top m) (ThetaVNoteD.lt_succ β) ?_
  rw [termVal_numI]
  exact (fix_smoke m t _ List.mem_cons_self).mono_height hβ (Set.mem_univ _)

/-! ### Smoke test 1: `⊢ Jlev ⊤ (0̄, 0̄)` -/

theorem smoke_jlev_zero :
    IDwDerivable smokeA ThetaVNoteD.zero Htriv (ThetaVNoteD.succ (ThetaVNoteD.Omega 0))
      [jlevAt ⊤ (numI 0) (numI 0)] :=
  jlevTop_derivable 0 (numI 0) _ (numI_freeVariables 0) List.mem_cons_self le_rfl

/-! ### Smoke test 2: `⊢ ∀y (y < 2 → Jlev ⊤ (y, 0̄))` below `Ω_3` -/

/-- `s < t` in `LIinfW`. -/
def ltI {ξ : Type*} {m : ℕ} (s t : Semiterm LIinfW ξ m) : Semiformula LIinfW ξ m :=
  Semiformula.rel (Sum.inl Language.LT.lt : LIinfW.Rel 2) ![s, t]

/-- `y < 2 → Jlev ⊤ (y, 0̄)`, as `¬(y < 2) ∨ Jlev ⊤ (y, 0̄)`, with the bound variable `y = #0`. -/
def phiLt2 : Semiproposition LIinfW 1 :=
  ∼(ltI (#0 : Semiterm LIinfW ℕ 1) ((2 : ℕ) : Semiterm LIinfW ℕ 1)) ⋎
    jlevAt ⊤ (#0 : Semiterm LIinfW ℕ 1) ((0 : ℕ) : Semiterm LIinfW ℕ 1)

theorem subst_rel_num (m : ℕ) (r : LIinfW.Rel 2) (k : ℕ) :
    ((Rew.subst ![numI m]) ▹ (Semiformula.rel r ![(#0 : Semiterm LIinfW ℕ 1),
      ((k : ℕ) : Semiterm LIinfW ℕ 1)] : Semiformula LIinfW ℕ 1) : Proposition LIinfW) =
      Semiformula.rel r ![numI m, numI k] := by
  rw [Semiformula.rew_rel]
  congr 1
  funext i
  match i with
  | 0 => simp
  | 1 => simp [numI]

theorem phiLt2_subst (m : ℕ) :
    (phiLt2/[numI m] : Proposition LIinfW) =
      ∼(ltI (numI m) (numI 2)) ⋎ jlevAt ⊤ (numI m) (numI 0) := by
  simp only [phiLt2, ltI, jlevAt]
  simp
  exact ⟨subst_rel_num m _ 2, subst_rel_num m _ 0⟩

theorem trueN_ltI (a b : ℕ) : TrueN (ltI (numI a) (numI b)) ↔ a < b := by
  unfold TrueN ltI
  refine (Semiformula.eval_rel (s := stdW) (b := ![]) (f := fun _ => 0)
    (r := (Sum.inl Language.LT.lt : LIinfW.Rel 2)) (v := ![numI a, numI b])).trans ?_
  have e : (Semiterm.val (s := stdW) ![] (fun _ => 0)) ∘ ![numI a, numI b] = ![a, b] := by
    funext i
    match i with
    | 0 => exact val_numI a _ _
    | 1 => exact val_numI b _ _
  simp only [e]
  show Structure.rel (L := ℒₒᵣ) (Language.LT.lt : Language.Rel ℒₒᵣ 2) ![a, b] ↔ a < b
  simp

theorem trueLit_not_lt (m : ℕ) (h : 2 ≤ m) : TrueLit (∼(ltI (numI m) (numI 2))) := by
  refine ⟨⟨2, Language.LT.lt, ![numI m, numI 2], Or.inr rfl, ?_⟩, ?_⟩
  · intro i
    match i with
    | 0 => exact numI_freeVariables m
    | 1 => exact numI_freeVariables 2
  · rw [trueN_neg]
    intro hh
    exact absurd ((trueN_ltI m 2).mp hh) (by omega)

theorem Omega_le_Omega_one {m : ℕ} (hm : m < 2) :
    ThetaVNoteD.Omega m ≤ ThetaVNoteD.Omega 1 := by
  rcases m with _ | _ | m
  · exact (Omega_lt_Omega (by omega)).le
  · exact le_rfl
  · omega

/-- **`⊢ ∀y (y < 2 → Jlev ⊤ (y, 0̄))`**: the ω-rule over `y`; for `y ≥ 2` the antecedent is a false
literal (`literal`), for `y < 2` the disjunct `Jlev ⊤ (ȳ, 0̄)` is derived by `jlev` + `fix` at level
`y ∈ {0, 1}`, whence the height `Ω_2 + 3 ≺ Ω_3` (`smoke_jlev_lt_two_lt`). -/
theorem smoke_jlev_lt_two :
    IDwDerivable smokeA ThetaVNoteD.zero Htriv
      (ThetaVNoteD.succ (ThetaVNoteD.succ (ThetaVNoteD.succ (ThetaVNoteD.Omega 1))))
      [∀¹ phiLt2] := by
  have hA : ThetaVNoteD.succ (ThetaVNoteD.Omega 1) <
      ThetaVNoteD.succ (ThetaVNoteD.succ (ThetaVNoteD.Omega 1)) := ThetaVNoteD.lt_succ _
  have hB : ThetaVNoteD.succ (ThetaVNoteD.succ (ThetaVNoteD.Omega 1)) <
      ThetaVNoteD.succ (ThetaVNoteD.succ (ThetaVNoteD.succ (ThetaVNoteD.Omega 1))) :=
    ThetaVNoteD.lt_succ _
  have hone : ThetaVNoteD.one <
      ThetaVNoteD.succ (ThetaVNoteD.succ (ThetaVNoteD.Omega 1)) :=
    lt_trans (one_lt_Omega 1) (lt_trans (ThetaVNoteD.lt_succ _) hA)
  refine .all (fun _ => ThetaVNoteD.succ (ThetaVNoteD.succ (ThetaVNoteD.Omega 1)))
    (Set.mem_univ _) (Set.subset_univ _) List.mem_cons_self (fun _ => hB) fun m => ?_
  rw [phiLt2_subst]
  by_cases hm : m < 2
  · refine .orR (Set.mem_univ _) (Set.subset_univ _) List.mem_cons_self hone hA ?_
    exact jlevTop_derivable m (numI 0) _ (numI_freeVariables 0) List.mem_cons_self
      (Omega_le_Omega_one hm)
  · refine .orL (Set.mem_univ _) (Set.subset_univ _) List.mem_cons_self
      (lt_trans (zero_lt_Omega 1) (lt_trans (ThetaVNoteD.lt_succ _) hA)) ?_
    exact .literal (Set.mem_univ _) (Set.subset_univ _) (trueLit_not_lt m (by omega))
      List.mem_cons_self

/-- The height of `smoke_jlev_lt_two` is below `Ω_3`. -/
theorem smoke_jlev_lt_two_lt :
    ThetaVNoteD.succ (ThetaVNoteD.succ (ThetaVNoteD.succ (ThetaVNoteD.Omega 1))) <
      ThetaVNoteD.Omega 2 :=
  succ_lt_Omega (succ_lt_Omega (succ_lt_Omega (Omega_lt_Omega (by omega))))

/-! ### Smoke test 3: `⊢ ∀y Jlev ⊤ (y, y)` at height `Ω_ω` -/

/-- `Jlev ⊤ (y, y)`, with the bound variable `y = #0`. -/
def phiAll : Semiproposition LIinfW 1 :=
  jlevAt ⊤ (#0 : Semiterm LIinfW ℕ 1) (#0 : Semiterm LIinfW ℕ 1)

theorem phiAll_subst (m : ℕ) :
    (phiAll/[numI m] : Proposition LIinfW) = jlevAt ⊤ (numI m) (numI m) := by
  show (Rew.subst ![numI m]) ▹ (jlevAt ⊤ _ _ : Semiformula LIinfW ℕ 1) = _
  simp only [jlevAt]
  refine (Semiformula.rew_rel (Rew.subst ![numI m])
    (Sum.inr (IInfRelW.jlev ⊤) : LIinfW.Rel 2) _).trans ?_
  congr 1
  funext i
  match i with
  | 0 => simp
  | 1 => simp

/-- **`⊢ ∀y Jlev ⊤ (y, y)`** at height `Ω_ω`: instance `m` needs `fix` at level `m`, height
`Ω_{m+1} + 1`, unbounded below `Ω_ω` and below no smaller height. -/
theorem smoke_jlev_all :
    IDwDerivable smokeA ThetaVNoteD.zero Htriv ThetaVNoteD.OmegaW [∀¹ phiAll] :=
  .all (fun m => ThetaVNoteD.succ (ThetaVNoteD.Omega m)) (Set.mem_univ _) (Set.subset_univ _)
    List.mem_cons_self (fun m => succ_lt_OmegaW (ThetaVNoteD.Omega_lt_OmegaW m)) fun m => by
      rw [phiAll_subst]
      exact jlevTop_derivable m (numI m) _ (numI_freeVariables m) List.mem_cons_self le_rfl

/-! ### Smoke tests for `njlev` -/

/-- **An empty conjunction**: `val s = 1 ≥ 1 = ℓ`, so `¬Jlev 1 (1̄, 0̄)` has no premise. -/
theorem smoke_njlev_empty :
    IDwDerivable smokeA ThetaVNoteD.zero Htriv ThetaVNoteD.zero
      [njlevAt (1 : WithTop ℕ) (numI 1) (numI 0)] := by
  refine IDwDerivable.njlev (α₀ := ThetaVNoteD.zero) (Set.mem_univ _) (Set.subset_univ _)
    List.mem_cons_self (numI_freeVariables 1)
    (numI_freeVariables 0) (fun h => ?_) (fun h => ?_) <;>
  · rw [termVal_numI] at h
    exact absurd h (by simp)

/-- **`njlev` with its premise**: `val s = 0 < 1 = ℓ`, premise `Γ, ¬I_0 0̄` (height `Ω_1 + 1`),
in which `Jlev ⊤ (0̄, 0̄)` is derived by `jlev` + `fix₀`. -/
theorem smoke_njlev_prem :
    IDwDerivable smokeA ThetaVNoteD.zero Htriv
      (ThetaVNoteD.succ (ThetaVNoteD.succ (ThetaVNoteD.Omega 0)))
      [njlevAt (1 : WithTop ℕ) (numI 0) (numI 0), jlevAt ⊤ (numI 0) (numI 0)] := by
  refine .njlev (Set.mem_univ _) (Set.subset_univ _) List.mem_cons_self (numI_freeVariables 0)
    (numI_freeVariables 0) (fun _ => ThetaVNoteD.lt_succ _) fun _ => ?_
  exact jlevTop_derivable 0 (numI 0) _ (numI_freeVariables 0)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) le_rfl

end IDw

end OrdinalAnalysis
