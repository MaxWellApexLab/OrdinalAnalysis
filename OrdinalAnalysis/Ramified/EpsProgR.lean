/-
  ε-progressiveness and Gentzen's bound at a level `μ` of ramified analysis.

  With `TI_μ(a) :≡ ∀z TI(≺₁, a, λx. x ∈̇_μ z)` (`Ramified/TowerR.lean`), let

      ψ_μ(g) :≡ ∀u (Eps(u, g) → TI_μ(u)),

  "transfinite induction holds below `ε_g` for every level-`μ` set", the value
  `ε_g` being named by the internal graph `Eps`.  For `0 < μ < ν`:

  * **(EP_μ)** `RAlt ν ⊢ Prog(≺₁, ψ_μ)` (`epsProg_provable`).  Let every `h ≺₁ g`
    satisfy `ψ_μ`, let `u = ε_g`, `z` a level-`μ` set progressive along `≺₁`,
    and `x ≺₁ u`.  The internal ε-cover gives a tower `w` of height `n` over a
    good base `s` with `x ≺₁ w`.  A good base is `0 + 1`, or `ε_h + 1` with
    `h ≺₁ g`; in both cases `TI_μ` holds at the base (trivially at `0`, by the
    hypothesis `ψ_μ(h)` at `ε_h`) and passes to the successor.  The tower
    induction (Tw_μ) carries `TI_μ` from `s` to `w`, and `TI(≺₁, w, z)` gives
    `x ∈̇_μ z`.

  * **(G_μ)** `RAlt ν ⊢ TI(≺₁, c̄, ψ_μ)` for every external `c < ε₀`
    (`tiPsi_provable`): Gentzen's bound `PA[X] ⊢ TI(≺₁, c̄, X)`, lifted at the
    predicate defined by the level-`μ` formula `ψ_μ`.  This is the one place
    where the induction scheme of `RAlt ν` is used for a formula rather than a
    set: the instances of induction that the lifted `PA[X]`-proof needs are
    instances for formulas built from `ψ_μ`, all of level `μ`.

  * **(A_μ)** `RAlt ν ⊢ TI_μ(ε̄_c)` for every external `c < ε₀`
    (`ti_epsilon_provable`): `ψ_μ` is progressive and holds below `c̄`, hence at
    `c̄`, and `Eps(ε̄_c, c̄)`.

  As in `Ramified/TowerR.lean`, everything is proved in a model of `RAlt ν` with
  true equality and turned into provability by `provable_of_eqModels`.
-/
import OrdinalAnalysis.Ramified.TowerR

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen (LX paLX)
open OrdinalAnalysis.Gentzen.InternalVNote (precDef₁)
open OrdinalAnalysis.Gentzen.InternalEpsMonoCode (epsDef₁)
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)
open OrdinalAnalysis.Gamma0Note (epsilonNote)

/-! ### Progressiveness and transfinite induction for a formula of `LRA` -/

/-- `Prog(≺₁, φ) :≡ ∀x ((∀y ≺₁ x, φ(y)) → φ(x))`. -/
def progR (φ : Semiformula LRA ℕ 1) : Semiformula LRA ℕ 0 :=
  ∀¹ (∼(∀¹ (∼(arAt precDef₁.val ![(#0 : Semiterm LRA ℕ 2), #1]) ⋎
      φ/[(#0 : Semiterm LRA ℕ 2)])) ⋎ φ/[(#0 : Semiterm LRA ℕ 1)])

/-- `TI(≺₁, t, φ) :≡ Prog(≺₁, φ) → ∀y ≺₁ t, φ(y)`. -/
def tiUpR (φ : Semiformula LRA ℕ 1) (t : Semiterm LRA ℕ 0) : Semiformula LRA ℕ 0 :=
  ∼(progR φ) ⋎ (∀¹ (∼(arAt precDef₁.val ![(#0 : Semiterm LRA ℕ 1), Rew.bShift t]) ⋎
    φ/[(#0 : Semiterm LRA ℕ 1)]))

theorem lvlOf_progR (φ : Semiformula LRA ℕ 1) : lvlOf (progR φ) = lvlOf φ := by
  simp [progR]

theorem lvlOf_tiUpR (φ : Semiformula LRA ℕ 1) (t : Semiterm LRA ℕ 0) :
    lvlOf (tiUpR φ t) = lvlOf φ := by
  simp [tiUpR, lvlOf_progR]

section Eval

variable {M : Type} [s : Structure LRA M]

private theorem eval_subst_bvar_one {n : ℕ} (φ : Semiformula LRA ℕ 1) (x : M) (e : Fin n → M)
    (f : ℕ → M) :
    Semiformula.Eval (s := s) (x :> e) f (φ/[(#0 : Semiterm LRA ℕ (n + 1))]) ↔
      Semiformula.Eval (s := s) ![x] f φ := by
  rw [Semiformula.eval_substs]
  have h : (Semiterm.val (s := s) (x :> e) f ∘ ![(#0 : Semiterm LRA ℕ (n + 1))]) = ![x] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  rw [h]

theorem eval_progR (φ : Semiformula LRA ℕ 1) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (progR φ) ↔
      ProgM (fun x => Semiformula.Eval (s := s) ![x] f φ) := by
  simp only [progR, Semiformula.eval_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq, eval_arAt, eval_subst_bvar_one]
  unfold ProgM
  refine forall_congr' fun x => ?_
  have hp : ∀ y : M, arEval precDef₁.val (fun i => Semiterm.val (s := s) (y :> x :> ![]) f
      (![(#0 : Semiterm LRA ℕ 2), #1] i)) ↔ precM y x := by
    intro y
    have hv : (fun i => Semiterm.val (s := s) (y :> x :> ![]) f
        (![(#0 : Semiterm LRA ℕ 2), #1] i)) = ![y, x] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    rfl
  simp only [hp]
  constructor
  · rintro (h | h) hb
    · exact absurd (fun y => imp_iff_not_or.mp (hb y)) h
    · exact h
  · intro h
    by_cases hb : ∀ y, precM y x → Semiformula.Eval (s := s) ![y] f φ
    · exact Or.inr (h hb)
    · exact Or.inl fun hall => hb fun y hy => (hall y).resolve_left (not_not_intro hy)

theorem eval_tiUpR (φ : Semiformula LRA ℕ 1) (t : Semiterm LRA ℕ 0) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (tiUpR φ t) ↔
      TIupM (fun x => Semiformula.Eval (s := s) ![x] f φ) (Semiterm.val (s := s) ![] f t) := by
  rw [tiUpR, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, eval_progR]
  simp only [LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq, Semiformula.eval_all,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, eval_arAt,
    eval_subst_bvar_one]
  have hp : ∀ y : M, arEval precDef₁.val (fun i => Semiterm.val (s := s) (y :> ![]) f
      (![(#0 : Semiterm LRA ℕ 1), Rew.bShift t] i)) ↔ precM y (Semiterm.val (s := s) ![] f t) := by
    intro y
    have hv : (fun i => Semiterm.val (s := s) (y :> ![]) f
        (![(#0 : Semiterm LRA ℕ 1), Rew.bShift t] i)) = ![y, Semiterm.val (s := s) ![] f t] := by
      funext i
      fin_cases i
      · rfl
      · exact Semiterm.val_bShift y t
    rw [hv]
    rfl
  simp only [hp]
  unfold TIupM
  constructor
  · rintro (h | h) hprog y hy
    · exact absurd hprog h
    · exact (h y).resolve_left (not_not_intro hy)
  · intro h
    by_cases hprog : ProgM (fun x => Semiformula.Eval (s := s) ![x] f φ)
    · exact Or.inr fun y => imp_iff_not_or.mp (h hprog y)
    · exact Or.inl hprog

end Eval

/-! ### The formula `ψ_μ` -/

/-- **`ψ_μ(g) :≡ ∀u (Eps(u, g) → TI_μ(u))`**, with `g` the bound variable. -/
def psiR (μ : Lv) : Semiformula LRA ℕ 1 :=
  ∀¹ (∼(arAt epsDef₁.val ![(#0 : Semiterm LRA ℕ 2), #1]) ⋎ (tiMuR μ)/[(#0 : Semiterm LRA ℕ 2)])

theorem lvlOf_psiR_le (μ : Lv) : lvlOf (psiR μ) ≤ μ := by
  simp only [psiR, lvlOf_all, lvlOf_or, lvlOf_neg, lvlOf_arAt, lvlOf_subst₁]
  exact max_le (Gamma0Note.zero_le_note μ) (lvlOf_tiMuR_le μ)

section Psi

variable {M : Type} [s : Structure LRA M]

/-- `ψ_μ(g)` in `M`. -/
def PsiM (μ : Lv) (g : M) : Prop := ∀ u : M, epsM u g → TImu μ u

theorem eval_psiR (μ : Lv) (g : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![g] f (psiR μ) ↔ PsiM μ g := by
  simp only [psiR, Semiformula.eval_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq, eval_arAt, eval_tiMuR_subst, Semiterm.val_bvar,
    Matrix.cons_val_zero]
  refine forall_congr' fun u => ?_
  have he : arEval epsDef₁.val (fun i => Semiterm.val (s := s) (u :> ![g]) f
      (![(#0 : Semiterm LRA ℕ 2), #1] i)) ↔ epsM u g := by
    have hv : (fun i => Semiterm.val (s := s) (u :> ![g]) f
        (![(#0 : Semiterm LRA ℕ 2), #1] i)) = ![u, g] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    rfl
  rw [he, imp_iff_not_or]

theorem definableLt_psi [Nonempty M] {ν μ : Lv} (hμ : μ < ν) :
    DefinableLt (M := M) ν (PsiM μ) :=
  ⟨psiR μ, lt_of_le_of_lt (lvlOf_psiR_le μ) hμ, fun _ => Classical.arbitrary M,
    fun g => (eval_psiR μ g _).symm⟩

end Psi

/-! ### (EP_μ), (G_μ), (A_μ) in a model -/

section Model

variable {M : Type} [Nonempty M] [s : Structure LRA M] [Structure.Eq LRA M] {ν μ : Lv}
  (hM : M↓[LRA] ⊧* RAlt ν)
include hM

/-- `TI_μ` holds below `0`: nothing is below `0`. -/
theorem TImu_zero (hν : 1 ≤ ν) : TImu μ (numVal M 0) :=
  fun _ _ y hy => absurd hy (not_precM_zero hM hν y)

/-- `TI_μ` passes from a base `e` to `e + 1`. -/
theorem TImu_succ (hμ : μ < ν) {e s₀ : M} (hb : baseM e) (ha : addM s₀ e oneM)
    (h : TImu μ e) : TImu μ s₀ :=
  fun z => succTI_M hM (definableLt_mem hμ z) hb ha (h z)

/-- **`TI_μ` at a good base**, given `ψ_μ` below `g`. -/
theorem good_TImu (hμ : μ < ν) (hν : 1 ≤ ν) {g s₀ : M} (hg : ∀ h, precM h g → PsiM μ h)
    (hgood : goodM s₀ g) : TImu μ s₀ := by
  rcases hgood with ⟨hb0, ha0⟩ | ⟨h, e, hh, hbe, heps, hae⟩
  · exact TImu_succ hM hμ hb0 ha0 (TImu_zero hM hν)
  · exact TImu_succ hM hμ hbe hae (hg h hh e heps)

/-- **(EP_μ) in a model**: `ψ_μ` is progressive along `≺₁`. -/
theorem epsProg_M (h0 : 0 < μ) (hμ : μ < ν) : ProgM (PsiM (M := M) μ) := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos (lt_trans h0 hμ)
  intro g hg u heu z hprog x hx
  obtain ⟨s₀, n, w, hgood, htw, hxw⟩ := cover_M hM hν heu hx
  have hs : TImu μ s₀ := good_TImu hM hμ hν hg hgood
  exact tower_TImu hM h0 hμ n s₀ w htw hs z hprog x hxw

/-- **(G_μ) in a model**: `TI(≺₁, c̄, ψ_μ)` for every external `c < ε₀`. -/
theorem tiPsi_M (hμ : μ < ν) {c : Gamma0Note} (hc : c < epsilonNote 0) :
    TIupM (PsiM μ) (numVal M (gamma0Code c)) :=
  tiUp_code hM (definableLt_psi hμ) hc

/-- `ψ_μ(c̄)` for every external `c < ε₀`. -/
theorem psi_code_M (h0 : 0 < μ) (hμ : μ < ν) {c : Gamma0Note} (hc : c < epsilonNote 0) :
    PsiM μ (numVal M (gamma0Code c)) :=
  epsProg_M hM h0 hμ _ (tiPsi_M hM hμ hc (epsProg_M hM h0 hμ))

/-- **(A_μ) in a model**: `TI_μ(ε̄_c)` for every external `c < ε₀`. -/
theorem ti_epsilon_M (h0 : 0 < μ) (hμ : μ < ν) {c : Gamma0Note} (hc : c < epsilonNote 0) :
    TImu μ (numVal M (gamma0Code (epsilonNote c))) := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos (lt_trans h0 hμ)
  exact psi_code_M hM h0 hμ hc _ (epsM_code hM hν c)

end Model

/-! ### The provable forms -/

/-- **(EP_μ)**: `RAlt ν ⊢ Prog(≺₁, ψ_μ)`, for `0 < μ < ν`. -/
theorem epsProg_provable {ν μ : Lv} (h0 : 0 < μ) (hμ : μ < ν) :
    RAlt ν ⊢ Semiformula.univCl (progR (psiR μ)) := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos (lt_trans h0 hμ)
  refine provable_of_eqModels hν ?_ ?_
  · rw [lvlOf_emb_univCl, lvlOf_progR]
    exact lt_of_le_of_lt (lvlOf_psiR_le μ) hμ
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f (progR (psiR μ))
    rw [eval_progR]
    have h := epsProg_M hN h0 hμ
    intro x hx
    exact (eval_psiR μ x f).mpr (h x fun y hy => (eval_psiR μ y f).mp (hx y hy))

/-- **(G_μ)**: `RAlt ν ⊢ TI(≺₁, c̄, ψ_μ)` for every external `c < ε₀`, `μ < ν`. -/
theorem tiPsi_provable {ν μ : Lv} (hμ : μ < ν) {c : Gamma0Note} (hc : c < epsilonNote 0) :
    RAlt ν ⊢ Semiformula.univCl (tiUpR (psiR μ) (numAtR (gamma0Code c))) := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos (lt_of_le_of_lt (Gamma0Note.zero_le_note μ) hμ)
  refine provable_of_eqModels hν ?_ ?_
  · rw [lvlOf_emb_univCl, lvlOf_tiUpR]
    exact lt_of_le_of_lt (lvlOf_psiR_le μ) hμ
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f (tiUpR (psiR μ) (numAtR (gamma0Code c)))
    rw [eval_tiUpR, val_numAtR_model]
    have hP : (fun x => Semiformula.Eval (s := sN) ![x] f (psiR μ)) = PsiM μ :=
      funext fun x => propext (eval_psiR μ x f)
    rw [hP]
    exact tiPsi_M hN hμ hc

/-- **(A_μ)**: `RAlt ν ⊢ TI_μ(ε̄_c)` for every external `c < ε₀`, `0 < μ < ν`. -/
theorem ti_epsilon_provable {ν μ : Lv} (h0 : 0 < μ) (hμ : μ < ν) {c : Gamma0Note}
    (hc : c < epsilonNote 0) :
    RAlt ν ⊢ Semiformula.univCl ((tiMuR μ)/[(numAtR (gamma0Code (epsilonNote c)) :
      Semiterm LRA ℕ 0)]) := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos (lt_trans h0 hμ)
  refine provable_of_eqModels hν ?_ ?_
  · rw [lvlOf_emb_univCl, lvlOf_subst₁]
    exact lt_of_le_of_lt (lvlOf_tiMuR_le μ) hμ
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f ((tiMuR μ)/[(numAtR (gamma0Code (epsilonNote c)) :
      Semiterm LRA ℕ 0)])
    rw [eval_tiMuR_subst, val_numAtR_model]
    exact ti_epsilon_M hN h0 hμ hc

end Ramified

end OrdinalAnalysis
