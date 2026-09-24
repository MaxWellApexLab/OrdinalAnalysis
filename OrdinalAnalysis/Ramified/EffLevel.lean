/-
  The effective body of a name: every level-`L` name `z̄` is extensionally a
  formula of level below `L`, uniformly, in `RA_∞` with the junk literals.

  A `Good` code `z` of level `L` may mention level-`L` sets, but only through its
  parameter `p = param z`, whose stage is smaller (`Ramified/Code.lean`).  Unfold
  the parameter atoms `t ∈̇_L p̄` of the body into the body of `p`, and so on down
  the parameter chain: the recursion on the stage terminates, and at its end the
  parameter is either a `Good` code of level `L` whose body mentions no level-`L`
  set, or a junk name, which denotes the empty set.  The result is

      effBody z : Semiformula LRA ℕ 1,        lvlOf (effBody z) < lvl z,

  a closed formula (`freeVariables_effBodyAt`) in the subject `#0`.

  ## Definitions

  * `rp L B A` replaces every level-`L` atom `t ∈̇_L s` of `A` by `B(t)` and every
    `t ∉̇_L s` by `∼B(t)`, whatever `s` is; for `A` of shape `L` the set argument
    is always the parameter `&0`.  `lvlOf_rp_lt`: if `A` has shape `L` and
    `lvlOf B < L` then `lvlOf (rp L B A) < L`.

  * `effBodyAt L z`: if `z` is `Good` of level `L`, its formula with the level-`L`
    atoms replaced by `effBodyAt L (param z)`, the parameter then instantiated by
    its numeral; otherwise `⊥`.  Defined by well-founded recursion on
    `stage z`.  The parameter's level is not checked separately: a parameter
    that is not a `Good` code *of level `L`* is a junk name at level `L`, so its
    effective body at level `L` is `⊥`, which is what the junk literals say.
    `effBody z := effBodyAt (lvl z) z`.

  ## The unfolding (`effBodyAt_derivable`)

  For every `L`, `z` and ground subject `t` of value `y`, cut-free (so at every
  rank), from any literal set containing the junk literals, at height
  `2 · stage z`:

      ⊢ y ∉̇_L z̄, B(t)        and        ⊢ ∼B(t), y ∈̇_L z̄,        `B = effBodyAt L z`.

  By recursion on the stage.  At a junk `z` the first sequent is a junk axiom and
  the second contains `⊤`.  At a `Good` `z` of level `L`, one (Pr⁻), resp. (Pr),
  inference reduces the atom to the body; the replacement lemma `rp_derivable`,
  fed with the unfolding for the parameter, identifies the body with the
  effective body.  The replacement lemma is proved by induction on the formula
  under an arbitrary ground rewriting, at height `h + 2 · complexity`; the
  stage condition `complexity + stage p < stage z` of a `Good` code is exactly
  what keeps the total height at `2 · stage z`.

  Consequences:

  * `effBody_derivable`: the numeral form at the name's own level;
  * `effIff_derivable`: the sentence `∀y (y ∈̇_L z̄ ↔ B(y))` at height
    `2 · stage z + 3`; its rank is below `blkTop (L ⊕ 1)`
    (`rank_evR_effIff_lt`);
  * `effBodyAt_code_derivable`: for every `κ > lvlOf B`, the name `z̄` at level
    `L` and the parameter-free code `code κ B` at level `κ` have the same
    members, cut-free, at height `2 · stage z + 1`.  At a `Good` `z` one may take
    `κ < L`: this is how a level-`L` set with a same-level parameter is named at a
    lower level without parameters.

  Without the junk literals none of this holds at a junk name: `t ∈̇_L z̄` would
  then be an uninterpreted predicate.
-/
import OrdinalAnalysis.Ramified.InfTools

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder

/-! ### Replacing the atoms of one level -/

/-- A positive atom, with every level-`L` set atom `t ∈̇_L s` replaced by `B(t)`. -/
def repAtomP (L : Lv) (B : Semiformula LRA ℕ 1) :
    {j : ℕ} → LRA.Rel j → {k : ℕ} → (Fin j → Semiterm LRA ℕ k) → Semiformula LRA ℕ k
  | _, Sum.inl r, _, v => Semiformula.rel (Sum.inl r) v
  | _, Sum.inr RARel.X, _, v => Semiformula.rel (Sum.inr RARel.X) v
  | _, Sum.inr (RARel.mem κ), _, v =>
      if κ = L then Rew.subst ![v 0] ▹ B else Semiformula.rel (Sum.inr (RARel.mem κ)) v

/-- A negative atom, with every level-`L` set atom `t ∉̇_L s` replaced by `∼B(t)`. -/
def repAtomN (L : Lv) (B : Semiformula LRA ℕ 1) :
    {j : ℕ} → LRA.Rel j → {k : ℕ} → (Fin j → Semiterm LRA ℕ k) → Semiformula LRA ℕ k
  | _, Sum.inl r, _, v => Semiformula.nrel (Sum.inl r) v
  | _, Sum.inr RARel.X, _, v => Semiformula.nrel (Sum.inr RARel.X) v
  | _, Sum.inr (RARel.mem κ), _, v =>
      if κ = L then ∼(Rew.subst ![v 0] ▹ B) else Semiformula.nrel (Sum.inr (RARel.mem κ)) v

/-- **Replacement of the level-`L` atoms**: `t ∈̇_L s` becomes `B(t)` and `t ∉̇_L s`
becomes `∼B(t)`, whatever `s` is; everything else is kept. -/
def rp (L : Lv) (B : Semiformula LRA ℕ 1) : {k : ℕ} → Semiformula LRA ℕ k → Semiformula LRA ℕ k
  |  _, .rel r v => repAtomP L B r v
  | _, .nrel r v => repAtomN L B r v
  |         _, ⊤ => ⊤
  |         _, ⊥ => ⊥
  |     _, φ ⋏ ψ => rp L B φ ⋏ rp L B ψ
  |     _, φ ⋎ ψ => rp L B φ ⋎ rp L B ψ
  |      _, ∀¹ φ => ∀¹ rp L B φ
  |      _, ∃¹ φ => ∃¹ rp L B φ

section RpSimp

variable {L : Lv} {B : Semiformula LRA ℕ 1} {k : ℕ}

@[simp] theorem rp_verum : rp L B (⊤ : Semiformula LRA ℕ k) = ⊤ := rfl

@[simp] theorem rp_falsum : rp L B (⊥ : Semiformula LRA ℕ k) = ⊥ := rfl

@[simp] theorem rp_and (φ ψ : Semiformula LRA ℕ k) : rp L B (φ ⋏ ψ) = rp L B φ ⋏ rp L B ψ := rfl

@[simp] theorem rp_or (φ ψ : Semiformula LRA ℕ k) : rp L B (φ ⋎ ψ) = rp L B φ ⋎ rp L B ψ := rfl

@[simp] theorem rp_all (φ : Semiformula LRA ℕ (k + 1)) : rp L B (∀¹ φ) = ∀¹ rp L B φ := rfl

@[simp] theorem rp_exs (φ : Semiformula LRA ℕ (k + 1)) : rp L B (∃¹ φ) = ∃¹ rp L B φ := rfl

end RpSimp

/-- **The replacement lowers the level.**  If every level-`L` atom of `A` is at the
top level allowed by the shape, and `B` lies strictly below `L`, then the
replaced formula lies strictly below `L`. -/
theorem lvlOf_rp_lt {L : Lv} (hL : 0 < L) {B : Semiformula LRA ℕ 1} (hB : lvlOf B < L) :
    ∀ {k : ℕ} {A : Semiformula LRA ℕ k}, Shape L A → lvlOf (rp L B A) < L := by
  intro k A hA
  induction A using Semiformula.rec' with
  | hverum => rw [rp_verum, lvlOf_verum]; exact hL
  | hfalsum => rw [rp_falsum, lvlOf_falsum]; exact hL
  | hrel r v =>
      rcases r with r | r
      · exact lt_of_eq_of_lt (lvlOf_rel (Sum.inl r : LRA.Rel _) v) hL
      · cases r with
        | X =>
            exact lt_of_eq_of_lt (lvlOf_rel (Sum.inr RARel.X : LRA.Rel 1) v) hL
        | mem κ =>
            show lvlOf (if κ = L then Rew.subst ![v 0] ▹ B
              else Semiformula.rel (Sum.inr (RARel.mem κ)) v) < L
            by_cases hκ : κ = L
            · rw [if_pos hκ, lvlOf_rew]; exact hB
            · rw [if_neg hκ]
              rcases hA with h | ⟨h, -⟩
              · exact lt_of_eq_of_lt (lvlOf_rel (Sum.inr (RARel.mem κ) : LRA.Rel 2) v) h
              · exact absurd h hκ
  | hnrel r v =>
      rcases r with r | r
      · exact lt_of_eq_of_lt (lvlOf_nrel (Sum.inl r : LRA.Rel _) v) hL
      · cases r with
        | X =>
            exact lt_of_eq_of_lt (lvlOf_nrel (Sum.inr RARel.X : LRA.Rel 1) v) hL
        | mem κ =>
            show lvlOf (if κ = L then ∼(Rew.subst ![v 0] ▹ B)
              else Semiformula.nrel (Sum.inr (RARel.mem κ)) v) < L
            by_cases hκ : κ = L
            · rw [if_pos hκ, lvlOf_neg, lvlOf_rew]; exact hB
            · rw [if_neg hκ]
              rcases hA with h | ⟨h, -⟩
              · exact lt_of_eq_of_lt (lvlOf_nrel (Sum.inr (RARel.mem κ) : LRA.Rel 2) v) h
              · exact absurd h hκ
  | hand φ ψ ihφ ihψ => rw [rp_and, lvlOf_and]; exact max_lt (ihφ hA.1) (ihψ hA.2)
  | hor φ ψ ihφ ihψ => rw [rp_or, lvlOf_or]; exact max_lt (ihφ hA.1) (ihψ hA.2)
  | hall φ ih => rw [rp_all, lvlOf_all]; exact ih hA
  | hexs φ ih => rw [rp_exs, lvlOf_exs]; exact ih hA

/-! ### The effective body -/

open Classical in
/-- **The effective body of `z` at level `L`.**  If `z` is a `Good` code of level
`L`, its formula with every level-`L` atom (all of which have the parameter as
set argument, by the shape condition) replaced by the effective body of the
parameter, and the parameter then instantiated; otherwise `⊥`, the body of the
empty set a junk name denotes.  Recursion on the stage: the parameter of a
`Good` code has smaller stage. -/
noncomputable def effBodyAt (L : Lv) (z : ℕ) : Semiformula LRA ℕ 1 :=
  if _h : Good z ∧ lvl z = L then
    instParam (param z) ▹ rp L (effBodyAt L (param z)) (formula z)
  else ⊥
termination_by stage z
decreasing_by exact lt_of_le_of_lt (Nat.le_add_left _ _) (good_stage _h.1)

/-- **The effective body of a code**, at its own level. -/
noncomputable def effBody (z : ℕ) : Semiformula LRA ℕ 1 := effBodyAt (lvl z) z

theorem effBodyAt_of_good {L : Lv} {z : ℕ} (h : Good z ∧ lvl z = L) :
    effBodyAt L z = instParam (param z) ▹ rp L (effBodyAt L (param z)) (formula z) := by
  rw [effBodyAt, dif_pos h]

theorem effBodyAt_of_not {L : Lv} {z : ℕ} (h : ¬(Good z ∧ lvl z = L)) :
    effBodyAt L z = ⊥ := by
  rw [effBodyAt, dif_neg h]

/-- **The level of an effective body is below `L`**, for every positive `L`. -/
theorem lvlOf_effBodyAt_lt {L : Lv} (hL : 0 < L) (z : ℕ) : lvlOf (effBodyAt L z) < L := by
  induction z using (measure stage).wf.induction with
  | h z ih =>
      by_cases h : Good z ∧ lvl z = L
      · rw [effBodyAt_of_good h, lvlOf_rew]
        have hp : stage (param z) < stage z :=
          lt_of_le_of_lt (Nat.le_add_left _ _) (good_stage h.1)
        refine lvlOf_rp_lt hL (ih _ hp) ?_
        have hs := good_shape h.1
        rw [h.2] at hs
        exact hs
      · rw [effBodyAt_of_not h, lvlOf_falsum]; exact hL

/-- **The level of the effective body of a `Good` code is below the code's level.** -/
theorem lvlOf_effBody_lt {z : ℕ} (hz : Good z) : lvlOf (effBody z) < lvl z :=
  lvlOf_effBodyAt_lt (good_lvl_pos hz) z

/-- The effective body of a junk name is `⊥`. -/
theorem effBody_of_not_good {z : ℕ} (hz : ¬Good z) : effBody z = ⊥ :=
  effBodyAt_of_not fun h => hz h.1

/-- The effective body of a junk name has level `0`. -/
theorem lvlOf_effBody_of_not_good {z : ℕ} (hz : ¬Good z) : lvlOf (effBody z) = 0 := by
  rw [effBody_of_not_good hz, lvlOf_falsum]

/-- **The effective body is closed**: its only variable is the subject `#0`. -/
theorem freeVariables_effBodyAt (L : Lv) (z : ℕ) : (effBodyAt L z).freeVariables = ∅ := by
  by_cases h : Good z ∧ lvl z = L
  · rw [effBodyAt_of_good h]
    refine freeVariables_rew_eq_empty_of _ _ (fun i => ?_) (fun x => ?_)
    · rw [instParam_bvar, Semiterm.freeVariables_bvar]
    · rw [instParam_fvar]; exact freeVariables_of_groundR (groundR_numAtR _)
  · rw [effBodyAt_of_not h]; rfl

/-! ### Ground rewritings -/

/-- A rewriting that sends every variable, bound or free, to a ground term. -/
def GroundRew {k : ℕ} (ω : Rew LRA ℕ k ℕ 0) : Prop :=
  (∀ i : Fin k, GroundR (ω #i)) ∧ ∀ x : ℕ, GroundR (ω &x)

/-- A ground rewriting grounds every term. -/
theorem groundR_of_groundRew {k : ℕ} {ω : Rew LRA ℕ k ℕ 0} (hω : GroundRew ω) :
    ∀ t : Semiterm LRA ℕ k, GroundR (ω t) := by
  intro t
  induction t with
  | bvar x => exact hω.1 x
  | fvar x => exact hω.2 x
  | func f v ih =>
      rw [ω.func' f v]
      exact (groundR_func_iff f _).mpr ih

/-- Under a ground rewriting a term evaluates to the numeral of its value. -/
theorem evTR_groundRew {k : ℕ} {ω : Rew LRA ℕ k ℕ 0} (hω : GroundRew ω) (t : Semiterm LRA ℕ k) :
    evTR (ω t) = num (evTermR (ω t)) :=
  evTR_of_groundR (groundR_of_groundRew hω t)

/-- Lifting a ground rewriting under a binder and filling the new variable with a
numeral gives a ground rewriting, with the same values on the free variables. -/
theorem groundRew_substq {k : ℕ} {ω : Rew LRA ℕ k ℕ 0} (hω : GroundRew ω) (n : ℕ) :
    GroundRew ((Rew.subst ![num n]).comp ω.q) := by
  constructor
  · intro i
    induction i using Fin.cases with
    | zero => rw [Rew.comp_app, Rew.q_bvar_zero, Rew.subst_bvar]; exact groundR_num n
    | succ j =>
        rw [Rew.comp_app, Rew.q_bvar_succ]
        exact groundR_rew _ (groundR_rew _ (hω.1 j))
  · intro x
    rw [Rew.comp_app, Rew.q_fvar]
    exact groundR_rew _ (groundR_rew _ (hω.2 x))

theorem evTermR_substq_fvar {k : ℕ} {ω : Rew LRA ℕ k ℕ 0} (hω : GroundRew ω) (n x : ℕ) :
    evTermR (((Rew.subst ![num n]).comp ω.q) &x) = evTermR (ω &x) := by
  rw [Rew.comp_app, Rew.q_fvar, evTermR_rew _ (groundR_rew _ (hω.2 x)), evTermR_rew _ (hω.2 x)]

/-- The `n`-th instance of a quantified body under a rewriting is the body under
the lifted rewriting with `n̄` in the new place. -/
theorem inst_evR_rew_q {k : ℕ} (ω : Rew LRA ℕ k ℕ 0) (ψ : Semiformula LRA ℕ (k + 1)) (n : ℕ) :
    evInstR.inst (evR (ω.q ▹ ψ)) n = evR (((Rew.subst ![num n]).comp ω.q) ▹ ψ) := by
  rw [evInstR_inst_ev]
  exact congrArg evR (TransitiveRewriting.comp_app ω.q (Rew.subst ![num n]) ψ).symm

/-! ### Propositional and quantifier steps

The four steps of the replacement argument: from the two directions for the
components, the two directions for the compound, two inferences higher. -/

section Steps

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals LRA} {ρ : Gamma0Note}

/-- The finite heights are monotone. -/
theorem ofNat_le_ofNat' {m n : ℕ} (h : m ≤ n) :
    (OrdinalNotation.ofNat m : O) ≤ OrdinalNotation.ofNat n := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (OrdinalNotation.ofNat_lt_ofNat h)
  · exact le_rfl

theorem rpStep_and {m : ℕ} {X₁ X₂ Y₁ Y₂ : Proposition LRA}
    (h₁ : OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat m : O) [∼X₁, Y₁])
    (h₂ : OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat m : O) [∼X₂, Y₂]) :
    OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (m + 2) : O) [∼(X₁ ⋏ X₂), Y₁ ⋏ Y₂] := by
  show OmegaDerivableR A evInstR ρ _ [∼X₁ ⋎ ∼X₂, Y₁ ⋏ Y₂]
  refine .or (β := OrdinalNotation.ofNat (m + 1)) (OrdinalNotation.ofNat_lt_ofNat (by omega)) ?_
  refine .contraction (Δ := [Y₁ ⋏ Y₂, ∼X₁, ∼X₂])
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
  refine .and (OrdinalNotation.ofNat_lt_ofNat (by omega))
    (OrdinalNotation.ofNat_lt_ofNat (by omega))
    (.contraction (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) h₁)
    (.contraction (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) h₂)

theorem rpStep_or {m : ℕ} {X₁ X₂ Y₁ Y₂ : Proposition LRA}
    (h₁ : OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat m : O) [∼X₁, Y₁])
    (h₂ : OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat m : O) [∼X₂, Y₂]) :
    OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (m + 2) : O) [∼(X₁ ⋎ X₂), Y₁ ⋎ Y₂] := by
  show OmegaDerivableR A evInstR ρ _ [∼X₁ ⋏ ∼X₂, Y₁ ⋎ Y₂]
  refine .and (β := OrdinalNotation.ofNat (m + 1)) (γ := OrdinalNotation.ofNat (m + 1))
    (OrdinalNotation.ofNat_lt_ofNat (by omega)) (OrdinalNotation.ofNat_lt_ofNat (by omega)) ?_ ?_
  · refine .contraction (Δ := [Y₁ ⋎ Y₂, ∼X₁])
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
    refine .or (OrdinalNotation.ofNat_lt_ofNat (by omega)) (.contraction (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) h₁)
  · refine .contraction (Δ := [Y₁ ⋎ Y₂, ∼X₂])
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
    refine .or (OrdinalNotation.ofNat_lt_ofNat (by omega)) (.contraction (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) h₂)

theorem rpStep_all {m : ℕ} {X Y : Semiproposition LRA 1}
    (h : ∀ n : ℕ, OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat m : O)
      [∼(evInstR.inst X n), evInstR.inst Y n]) :
    OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (m + 2) : O) [∼(∀¹ X), ∀¹ Y] := by
  show OmegaDerivableR A evInstR ρ _ [∃¹ ∼X, ∀¹ Y]
  refine .contraction (Δ := [∀¹ Y, ∃¹ ∼X])
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
  refine .omegaRule (fun _ => OrdinalNotation.ofNat (m + 1))
    (fun _ => OrdinalNotation.ofNat_lt_ofNat (by omega)) (fun n => ?_)
  refine .contraction (Δ := [∃¹ ∼X, evInstR.inst Y n])
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
  refine .exs (β := OrdinalNotation.ofNat m) n (OrdinalNotation.ofNat_lt_ofNat (by omega)) ?_
  rw [InstantiationR.inst_neg]
  exact h n

theorem rpStep_exs {m : ℕ} {X Y : Semiproposition LRA 1}
    (h : ∀ n : ℕ, OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat m : O)
      [∼(evInstR.inst X n), evInstR.inst Y n]) :
    OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (m + 2) : O) [∼(∃¹ X), ∃¹ Y] := by
  show OmegaDerivableR A evInstR ρ _ [∀¹ ∼X, ∃¹ Y]
  refine .omegaRule (fun _ => OrdinalNotation.ofNat (m + 1))
    (fun _ => OrdinalNotation.ofNat_lt_ofNat (by omega)) (fun n => ?_)
  refine .contraction (Δ := [∃¹ Y, evInstR.inst (∼X) n])
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
  refine .exs (β := OrdinalNotation.ofNat m) n (OrdinalNotation.ofNat_lt_ofNat (by omega)) ?_
  rw [InstantiationR.inst_neg]
  exact .contraction
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) (h n)

/-- A formula against itself, both ways round. -/
theorem rpStep_self {m : ℕ} (X : Proposition LRA) (hm : 2 * X.complexity ≤ m) :
    OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat m : O) [∼X, X] :=
  .contraction (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
    ((OmegaDerivableR.identity_formula (A := A) (I := evInstR) (ρ := ρ) (O := O) X).mono_ord
      (ofNat_le_ofNat' hm))

end Steps

/-! ### The replacement lemma -/

section Replacement

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals LRA} {ρ : Gamma0Note}

/-- A formula the replacement does not touch is equivalent to its replacement. -/
theorem rp_self {L : Lv} {B : Semiformula LRA ℕ 1} {h k : ℕ} {F : Semiformula LRA ℕ k}
    (hF : rp L B F = F) (ω : Rew LRA ℕ k ℕ 0) :
    OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (h + 2 * F.complexity) : O)
        [∼evR (ω ▹ F), evR (ω ▹ rp L B F)] ∧
      OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (h + 2 * F.complexity) : O)
        [∼evR (ω ▹ rp L B F), evR (ω ▹ F)] := by
  rw [hF]
  have hc : 2 * (evR (ω ▹ F)).complexity ≤ h + 2 * F.complexity := by
    rw [complexity_evR, Semiformula.complexity_rew]; omega
  exact ⟨rpStep_self _ hc, rpStep_self _ hc⟩

/-- **The replacement lemma.**  Let every level-`L` atom whose set argument
denotes `p` be equivalent to `B`, at height `h`, at every ground subject.  Then
every formula `F` of shape `L` is equivalent to its replacement `rp L B F`,
under every ground rewriting that sends the parameter `&0` to a term of value
`p`, at height `h + 2 · complexity F`.  Cut-free. -/
theorem rp_derivable {L : Lv} {p : ℕ} {B : Semiformula LRA ℕ 1} {h : ℕ}
    (HB : ∀ σ : Rew LRA ℕ 1 ℕ 0, (∀ i, GroundR (σ #i)) →
      OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat h : O)
          [nmemAt L (num (evTermR (σ #0))) (num p), evR (σ ▹ B)] ∧
        OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat h : O)
          [∼evR (σ ▹ B), memAt L (num (evTermR (σ #0))) (num p)]) :
    ∀ {k : ℕ} (F : Semiformula LRA ℕ k), Shape L F →
      ∀ ω : Rew LRA ℕ k ℕ 0, GroundRew ω → evTermR (ω &0) = p →
        OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (h + 2 * F.complexity) : O)
            [∼evR (ω ▹ F), evR (ω ▹ rp L B F)] ∧
          OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (h + 2 * F.complexity) : O)
            [∼evR (ω ▹ rp L B F), evR (ω ▹ F)] := by
  intro k F
  induction F using Semiformula.rec' with
  | hverum => intro _ ω _ _; exact rp_self rfl ω
  | hfalsum => intro _ ω _ _; exact rp_self rfl ω
  | hrel r v =>
      intro hF ω hω hp
      rcases r with r | r
      · exact rp_self rfl ω
      · cases r with
        | X => exact rp_self rfl ω
        | mem κ =>
            by_cases hκ : κ = L
            · subst hκ
              have hv1 : v 1 = &0 := by
                rcases hF with h' | ⟨-, h'⟩
                · exact absurd h' (lt_irrefl _)
                · exact h'
              set σ : Rew LRA ℕ 1 ℕ 0 := ω.comp (Rew.subst ![v 0]) with hσ
              have h0 : σ #0 = ω (v 0) := by rw [hσ, Rew.comp_app, Rew.subst_bvar]; rfl
              have hgσ : ∀ i, GroundR (σ #i) := by
                intro i
                rw [Subsingleton.elim i 0, h0]
                exact groundR_of_groundRew hω _
              obtain ⟨H1, H2⟩ := HB σ hgσ
              rw [h0] at H1 H2
              have hX : evR (ω ▹ (Semiformula.rel (Sum.inr (RARel.mem κ) : LRA.Rel 2) v))
                  = memAt κ (num (evTermR (ω (v 0)))) (num p) := by
                have e : (fun i => evTR (ω (v i))) = ![num (evTermR (ω (v 0))), num p] := by
                  funext i
                  fin_cases i
                  · exact evTR_groundRew hω _
                  · show evTR (ω (v 1)) = num p
                    rw [evTR_groundRew hω, hv1, hp]
                exact congrArg (Semiformula.rel (Sum.inr (RARel.mem κ) : LRA.Rel 2)) e
              have hY : evR (ω ▹ rp κ B (Semiformula.rel (Sum.inr (RARel.mem κ) : LRA.Rel 2) v))
                  = evR (σ ▹ B) := by
                have e : rp κ B (Semiformula.rel (Sum.inr (RARel.mem κ) : LRA.Rel 2) v)
                    = Rew.subst ![v 0] ▹ B := if_pos rfl
                rw [e, hσ]
                exact congrArg evR (TransitiveRewriting.comp_app (Rew.subst ![v 0]) ω B).symm
              rw [hX, hY]
              exact ⟨H1.mono_ord (ofNat_le_ofNat' (Nat.le_add_right _ _)),
                H2.mono_ord (ofNat_le_ofNat' (Nat.le_add_right _ _))⟩
            · exact rp_self (F := Semiformula.rel (Sum.inr (RARel.mem κ) : LRA.Rel 2) v)
                (if_neg hκ) ω
  | hnrel r v =>
      intro hF ω hω hp
      rcases r with r | r
      · exact rp_self rfl ω
      · cases r with
        | X => exact rp_self rfl ω
        | mem κ =>
            by_cases hκ : κ = L
            · subst hκ
              have hv1 : v 1 = &0 := by
                rcases hF with h' | ⟨-, h'⟩
                · exact absurd h' (lt_irrefl _)
                · exact h'
              set σ : Rew LRA ℕ 1 ℕ 0 := ω.comp (Rew.subst ![v 0]) with hσ
              have h0 : σ #0 = ω (v 0) := by rw [hσ, Rew.comp_app, Rew.subst_bvar]; rfl
              have hgσ : ∀ i, GroundR (σ #i) := by
                intro i
                rw [Subsingleton.elim i 0, h0]
                exact groundR_of_groundRew hω _
              obtain ⟨H1, H2⟩ := HB σ hgσ
              rw [h0] at H1 H2
              have hX : evR (ω ▹ (Semiformula.nrel (Sum.inr (RARel.mem κ) : LRA.Rel 2) v))
                  = nmemAt κ (num (evTermR (ω (v 0)))) (num p) := by
                have e : (fun i => evTR (ω (v i))) = ![num (evTermR (ω (v 0))), num p] := by
                  funext i
                  fin_cases i
                  · exact evTR_groundRew hω _
                  · show evTR (ω (v 1)) = num p
                    rw [evTR_groundRew hω, hv1, hp]
                exact congrArg (Semiformula.nrel (Sum.inr (RARel.mem κ) : LRA.Rel 2)) e
              have hY : evR (ω ▹ rp κ B (Semiformula.nrel (Sum.inr (RARel.mem κ) : LRA.Rel 2) v))
                  = ∼evR (σ ▹ B) := by
                have e : rp κ B (Semiformula.nrel (Sum.inr (RARel.mem κ) : LRA.Rel 2) v)
                    = ∼(Rew.subst ![v 0] ▹ B) := if_pos rfl
                rw [e, LogicalConnective.HomClass.map_neg, evR_neg, hσ]
                exact congrArg (fun X => ∼evR X)
                  (TransitiveRewriting.comp_app (Rew.subst ![v 0]) ω B).symm
              have nn : (∼∼evR (σ ▹ B) : Proposition LRA) = evR (σ ▹ B) :=
                Semiformula.neg_neg _
              rw [hX, hY, nn]
              refine ⟨?_, ?_⟩
              · refine OmegaDerivableR.contraction (fun x hx => ?_)
                  (H2.mono_ord (ofNat_le_ofNat' (Nat.le_add_right _ _)))
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
                rcases hx with rfl | rfl
                · exact Or.inr rfl
                · exact Or.inl rfl
              · refine OmegaDerivableR.contraction (fun x hx => ?_)
                  (H1.mono_ord (ofNat_le_ofNat' (Nat.le_add_right _ _)))
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
                rcases hx with rfl | rfl
                · exact Or.inr rfl
                · exact Or.inl rfl
            · exact rp_self (F := Semiformula.nrel (Sum.inr (RARel.mem κ) : LRA.Rel 2) v)
                (if_neg hκ) ω
  | hand φ ψ ihφ ihψ =>
      intro hF ω hω hp
      obtain ⟨Hφ1, Hφ2⟩ := ihφ hF.1 ω hω hp
      obtain ⟨Hψ1, Hψ2⟩ := ihψ hF.2 ω hω hp
      have hm1 : h + 2 * φ.complexity ≤ h + 2 * max φ.complexity ψ.complexity := by omega
      have hm2 : h + 2 * ψ.complexity ≤ h + 2 * max φ.complexity ψ.complexity := by omega
      have hfin : h + 2 * max φ.complexity ψ.complexity + 2 ≤ h + 2 * (φ ⋏ ψ).complexity := by
        show _ ≤ h + 2 * (max φ.complexity ψ.complexity + 1); omega
      rw [rp_and, LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and, evR_and,
        evR_and]
      exact ⟨(rpStep_and (Hφ1.mono_ord (ofNat_le_ofNat' hm1))
          (Hψ1.mono_ord (ofNat_le_ofNat' hm2))).mono_ord (ofNat_le_ofNat' hfin),
        (rpStep_and (Hφ2.mono_ord (ofNat_le_ofNat' hm1))
          (Hψ2.mono_ord (ofNat_le_ofNat' hm2))).mono_ord (ofNat_le_ofNat' hfin)⟩
  | hor φ ψ ihφ ihψ =>
      intro hF ω hω hp
      obtain ⟨Hφ1, Hφ2⟩ := ihφ hF.1 ω hω hp
      obtain ⟨Hψ1, Hψ2⟩ := ihψ hF.2 ω hω hp
      have hm1 : h + 2 * φ.complexity ≤ h + 2 * max φ.complexity ψ.complexity := by omega
      have hm2 : h + 2 * ψ.complexity ≤ h + 2 * max φ.complexity ψ.complexity := by omega
      have hfin : h + 2 * max φ.complexity ψ.complexity + 2 ≤ h + 2 * (φ ⋎ ψ).complexity := by
        show _ ≤ h + 2 * (max φ.complexity ψ.complexity + 1); omega
      rw [rp_or, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or, evR_or,
        evR_or]
      exact ⟨(rpStep_or (Hφ1.mono_ord (ofNat_le_ofNat' hm1))
          (Hψ1.mono_ord (ofNat_le_ofNat' hm2))).mono_ord (ofNat_le_ofNat' hfin),
        (rpStep_or (Hφ2.mono_ord (ofNat_le_ofNat' hm1))
          (Hψ2.mono_ord (ofNat_le_ofNat' hm2))).mono_ord (ofNat_le_ofNat' hfin)⟩
  | hall φ ih =>
      intro hF ω hω hp
      have H := fun n : ℕ =>
        ih hF _ (groundRew_substq hω n) ((evTermR_substq_fvar hω n 0).trans hp)
      have hfin : h + 2 * φ.complexity + 2 ≤ h + 2 * (∀¹ φ).complexity := by
        show _ ≤ h + 2 * (φ.complexity + 1); omega
      rw [rp_all, Rewriting.app_all, Rewriting.app_all, evR_all, evR_all]
      refine ⟨(rpStep_all fun n => ?_).mono_ord (ofNat_le_ofNat' hfin),
        (rpStep_all fun n => ?_).mono_ord (ofNat_le_ofNat' hfin)⟩
      · rw [inst_evR_rew_q, inst_evR_rew_q]; exact (H n).1
      · rw [inst_evR_rew_q, inst_evR_rew_q]; exact (H n).2
  | hexs φ ih =>
      intro hF ω hω hp
      have H := fun n : ℕ =>
        ih hF _ (groundRew_substq hω n) ((evTermR_substq_fvar hω n 0).trans hp)
      have hfin : h + 2 * φ.complexity + 2 ≤ h + 2 * (∃¹ φ).complexity := by
        show _ ≤ h + 2 * (φ.complexity + 1); omega
      rw [rp_exs, Rewriting.app_exs, Rewriting.app_exs, evR_exs, evR_exs]
      refine ⟨(rpStep_exs fun n => ?_).mono_ord (ofNat_le_ofNat' hfin),
        (rpStep_exs fun n => ?_).mono_ord (ofNat_le_ofNat' hfin)⟩
      · rw [inst_evR_rew_q, inst_evR_rew_q]; exact (H n).1
      · rw [inst_evR_rew_q, inst_evR_rew_q]; exact (H n).2

end Replacement

/-! ### The unfolding of a name into its effective body -/

section Unfolding

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals LRA} {ρ : Gamma0Note}

/-- **The unfolding, under a ground subject.**  For every level `L` and every `z`,
the atom `t ∈̇_L z̄` is equivalent to `B_z(t)`, `B_z` the effective body of `z` at
level `L`, for every ground subject `t`: both directions are cut-free derivable
at height `2 · stage z`, from any literal set containing the junk literals.

By recursion on the stage.  At a `Good` code of level `L` one (Pr⁻), resp. (Pr),
inference unfolds the atom into the body, and the replacement lemma, fed with
the equivalence for the parameter (of smaller stage), turns the body into the
effective body.  At any other `z` the negated atom is a junk axiom and the
effective body is `⊥`. -/
theorem effBodyAt_derivable (hJ : ∀ φ, JunkAtom φ → A.T φ) (L : Lv) (z : ℕ) :
    ∀ σ : Rew LRA ℕ 1 ℕ 0, (∀ i, GroundR (σ #i)) →
      OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (2 * stage z) : O)
          [nmemAt L (num (evTermR (σ #0))) (num z), evR (σ ▹ effBodyAt L z)] ∧
        OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (2 * stage z) : O)
          [∼evR (σ ▹ effBodyAt L z), memAt L (num (evTermR (σ #0))) (num z)] := by
  induction z using (measure stage).wf.induction with
  | h z ih =>
      intro σ hσ
      by_cases hz : Good z ∧ lvl z = L
      · obtain ⟨hg, rfl⟩ := hz
        have hst : (formula z).complexity + stage (param z) < stage z := good_stage hg
        have HB := ih (param z) (lt_of_le_of_lt (Nat.le_add_left _ _) hst)
        set ω : Rew LRA ℕ 1 ℕ 0 := σ.comp (instParam (param z)) with hωdef
        have hω0 : ω #0 = σ #0 := by rw [hωdef, Rew.comp_app, instParam_bvar]
        have hωx : ∀ x : ℕ, ω &x = numAtR (param z) := by
          intro x; rw [hωdef, Rew.comp_app, instParam_fvar, rew_numAtR]
        have hω : GroundRew ω :=
          ⟨fun i => by rw [Subsingleton.elim i 0, hω0]; exact hσ 0,
            fun x => by rw [hωx]; exact groundR_numAtR _⟩
        have hωp : evTermR (ω &0) = param z := by rw [hωx, evTermR_numAtR]
        obtain ⟨R1, R2⟩ := rp_derivable HB (formula z) (good_shape hg) ω hω hωp
        have hE : evR (σ ▹ effBodyAt (lvl z) z)
            = evR (ω ▹ rp (lvl z) (effBodyAt (lvl z) (param z)) (formula z)) := by
          rw [effBodyAt_of_good ⟨hg, rfl⟩, hωdef]
          exact congrArg evR (TransitiveRewriting.comp_app (instParam (param z)) σ _).symm
        have hB : evInstR.inst (body z) (evTermR (σ #0)) = evR (ω ▹ formula z) := by
          rw [evInstR_inst]
          show evR (Rew.subst ![num (evTermR (σ #0))] ▹ (instParam (param z) ▹ formula z)) = _
          rw [← TransitiveRewriting.comp_app]
          refine evR_rew_congr _ _ _ _ ⟨fun i => ?_, fun x => ?_⟩
          · rw [Subsingleton.elim i 0, hω0, Rew.comp_app, instParam_bvar, Rew.subst_bvar,
              evTR_of_groundR (hσ 0)]
            exact evTR_num _
          · rw [hωx, Rew.comp_app, instParam_fvar, rew_numAtR]
        have hlt : (OrdinalNotation.ofNat (2 * stage (param z) + 2 * (formula z).complexity) : O)
            < OrdinalNotation.ofNat (2 * stage z) := OrdinalNotation.ofNat_lt_ofNat (by omega)
        refine ⟨?_, ?_⟩
        · refine OmegaDerivableR.npr (a := z) (n := evTermR (σ #0))
            (Γ := [evR (σ ▹ effBodyAt (lvl z) z)]) hg hlt ?_
          rw [hB, hE]
          exact R1
        · have hpr : OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (2 * stage z) : O)
              [memAt (lvl z) (num (evTermR (σ #0))) (num z), ∼evR (σ ▹ effBodyAt (lvl z) z)] := by
            refine OmegaDerivableR.pr (a := z) (n := evTermR (σ #0))
              (Γ := [∼evR (σ ▹ effBodyAt (lvl z) z)]) hg hlt ?_
            rw [hB, hE]
            exact .contraction (fun x hx => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) R2
          exact .contraction (fun x hx => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) hpr
      · rw [effBodyAt_of_not hz]
        refine ⟨?_, ?_⟩
        · exact .contraction (fun x hx => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
            (.atom (hJ _ ⟨L, evTermR (σ #0), z, rfl, hz⟩))
        · exact OmegaDerivableR.of_mem_verum (List.Mem.head _)

/-- **The unfolding at a numeral**: for every `z`, every level `L` and every `y`,
cut-free at height `2 · stage z`,

    ⊢ y ∉̇_L z̄, B(ȳ)        and        ⊢ ∼B(ȳ), y ∈̇_L z̄

with `B = effBodyAt L z`. -/
theorem effBodyAt_numeral_derivable (hJ : ∀ φ, JunkAtom φ → A.T φ) (L : Lv) (z y : ℕ) :
    OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (2 * stage z) : O)
        [nmemAt L (num y) (num z), evInstR.inst (effBodyAt L z) y] ∧
      OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (2 * stage z) : O)
        [∼evInstR.inst (effBodyAt L z) y, memAt L (num y) (num z)] := by
  have H := effBodyAt_derivable (O := O) (ρ := ρ) hJ L z (Rew.subst ![num y])
    (fun i => by rw [Subsingleton.elim i 0, Rew.subst_bvar]; exact groundR_num y)
  have e : evTermR ((Rew.subst ![num y] : Rew LRA ℕ 1 ℕ 0) #0) = y := by
    rw [Rew.subst_bvar]; exact evTermR_num y
  rw [e] at H
  exact H

/-- **The unfolding of a name at its own level** (`L = lvl z`), in the junk-literal
calculus: for every `z` and `y`, cut-free at height `2 · stage z`,

    ⊢ y ∉̇_L z̄, B_z(ȳ)        and        ⊢ ∼B_z(ȳ), y ∈̇_L z̄

with `B_z = effBody z`, whose level is below `L` when `z` is `Good`, and which
is `⊥` when it is not. -/
theorem effBody_derivable (z y : ℕ) :
    OmegaDerivableR junkLitsR evInstR ρ (OrdinalNotation.ofNat (2 * stage z) : O)
        [nmemAt (lvl z) (num y) (num z), evInstR.inst (effBody z) y] ∧
      OmegaDerivableR junkLitsR evInstR ρ (OrdinalNotation.ofNat (2 * stage z) : O)
        [∼evInstR.inst (effBody z) y, memAt (lvl z) (num y) (num z)] :=
  effBodyAt_numeral_derivable (fun _ h => Or.inr h) (lvl z) z y

end Unfolding

/-! ### The equivalence as one sentence -/

/-- `y ∈̇_L z̄ ↔ B(y)`, with `B` the effective body of `z` at level `L`, as a
formula in the subject `#0`. -/
noncomputable def effIff (L : Lv) (z : ℕ) : Semiformula LRA ℕ 1 :=
  memAt L (#0 : Semiterm LRA ℕ 1) (numAtR z) 🡘 effBodyAt L z

theorem inst_effIff (L : Lv) (z n : ℕ) :
    evInstR.inst (evR (effIff L z)) n
      = (∼memAt L (num n) (num z) ⋎ evInstR.inst (effBodyAt L z) n) ⋏
        (∼evInstR.inst (effBodyAt L z) n ⋎ memAt L (num n) (num z)) := by
  rw [evInstR_inst_ev, evInstR_inst]
  show evR (Rew.subst ![num n] ▹ (memAt L (#0 : Semiterm LRA ℕ 1) (numAtR z) 🡘 effBodyAt L z)) = _
  rw [LogicalConnective.HomClass.map_iff, rew_memAt, Rew.subst_bvar, rew_numAtR]
  show evR ((∼memAt L (![num n] 0) (numAtR z) ⋎ Rew.subst ![num n] ▹ effBodyAt L z) ⋏
      (∼(Rew.subst ![num n] ▹ effBodyAt L z) ⋎ memAt L (![num n] 0) (numAtR z))) = _
  rw [evR_and, evR_or, evR_or, evR_neg, evR_neg]
  have hm : evR (memAt L ((![num n] : Fin 1 → SyntacticTerm LRA) 0) (numAtR z))
      = memAt L (num n) (num z) := evR_memAt_num (n := 0) L n z
  rw [hm]

section Sentence

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals LRA} {ρ : Gamma0Note}

/-- **`RA_∞ ⊢ ∀y (y ∈̇_L z̄ ↔ B_z(y))`**, cut-free, at height `2 · stage z + 3`, for
every level `L` and every `z`. -/
theorem effIff_derivable (hJ : ∀ φ, JunkAtom φ → A.T φ) (L : Lv) (z : ℕ) :
    OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (2 * stage z + 3) : O)
      [evR (∀¹ effIff L z)] := by
  rw [evR_all]
  refine OmegaDerivableR.omegaRuleUniform (β := OrdinalNotation.ofNat (2 * stage z + 2))
    (OrdinalNotation.ofNat_lt_ofNat (by omega)) (fun n => ?_)
  obtain ⟨H1, H2⟩ := effBodyAt_numeral_derivable (O := O) (ρ := ρ) hJ L z n
  rw [inst_effIff]
  refine .and (β := OrdinalNotation.ofNat (2 * stage z + 1))
    (γ := OrdinalNotation.ofNat (2 * stage z + 1))
    (OrdinalNotation.ofNat_lt_ofNat (by omega)) (OrdinalNotation.ofNat_lt_ofNat (by omega)) ?_ ?_
  · exact .or (OrdinalNotation.ofNat_lt_ofNat (by omega)) H1
  · exact .or (OrdinalNotation.ofNat_lt_ofNat (by omega)) H2

/-- The equivalence sentence at the level of the name, in the junk-literal
calculus. -/
theorem effBody_iff_derivable (z : ℕ) :
    OmegaDerivableR junkLitsR evInstR ρ (OrdinalNotation.ofNat (2 * stage z + 3) : O)
      [evR (∀¹ effIff (lvl z) z)] :=
  effIff_derivable (fun _ h => Or.inr h) (lvl z) z

/-- The level of the equivalence sentence is the level of the name. -/
theorem lvlOf_effIff {L : Lv} (hL : 0 < L) (z : ℕ) : lvlOf (effIff L z) = L := by
  have h := lvlOf_effBodyAt_lt hL z
  show lvlOf ((∼memAt L (#0 : Semiterm LRA ℕ 1) (numAtR z) ⋎ effBodyAt L z) ⋏
    (∼effBodyAt L z ⋎ memAt L (#0 : Semiterm LRA ℕ 1) (numAtR z))) = L
  rw [lvlOf_and, lvlOf_or, lvlOf_or, lvlOf_neg, lvlOf_neg, lvlOf_memAt, max_eq_left h.le,
    max_eq_right h.le, max_self]

end Sentence

/-! ### A parameter-free name of the same set, at a lower level -/

/-- **The effective body has every shape above its level**: it is a legitimate
parameter-free comprehension formula at every level `κ > lvlOf B_z`. -/
theorem shape_effBodyAt {L κ : Lv} {z : ℕ} (hκ : lvlOf (effBodyAt L z) < κ) :
    Shape κ (effBodyAt L z) :=
  shape_of_lvlOf_lt hκ

/-- The canonical parameter-free code of the effective body at level `κ` is
`Good`, of level `κ`, with body the effective body itself. -/
theorem good_code_effBodyAt {L κ : Lv} {z : ℕ} (hκ : lvlOf (effBodyAt L z) < κ) :
    Good (code κ (effBodyAt L z)) ∧ lvl (code κ (effBodyAt L z)) = κ ∧
      body (code κ (effBodyAt L z)) = effBodyAt L z :=
  ⟨good_code hκ, lvl_code κ _, body_code (freeVariables_effBodyAt L z)⟩

section Code

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals LRA} {ρ : Gamma0Note}

/-- **A name and the parameter-free code of its effective body name the same
set.**  For every level `L`, every `z`, every `κ` above the level of
`B = effBodyAt L z`, and every `y`, cut-free at height `2 · stage z + 1`,

    ⊢ y ∉̇_L z̄, y ∈̇_κ c̄        and        ⊢ y ∉̇_κ c̄, y ∈̇_L z̄

with `c = code κ B`.  For a `Good` `z` of level `L` one may take `κ` below `L`
(`lvlOf_effBodyAt_lt`); this is how a level-`L` set with a same-level parameter
is copied down to a lower level. -/
theorem effBodyAt_code_derivable (hJ : ∀ φ, JunkAtom φ → A.T φ) (L : Lv) (z : ℕ) {κ : Lv}
    (hκ : lvlOf (effBodyAt L z) < κ) (y : ℕ) :
    OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (2 * stage z + 1) : O)
        [nmemAt L (num y) (num z), memAt κ (num y) (num (code κ (effBodyAt L z)))] ∧
      OmegaDerivableR A evInstR ρ (OrdinalNotation.ofNat (2 * stage z + 1) : O)
        [nmemAt κ (num y) (num (code κ (effBodyAt L z))), memAt L (num y) (num z)] := by
  obtain ⟨hg, hl, hb⟩ := good_code_effBodyAt (z := z) hκ
  obtain ⟨H1, H2⟩ := effBodyAt_numeral_derivable (O := O) (ρ := ρ) hJ L z y
  have hlt : (OrdinalNotation.ofNat (2 * stage z) : O) < OrdinalNotation.ofNat (2 * stage z + 1) :=
    OrdinalNotation.ofNat_lt_ofNat (by omega)
  have P1 := OmegaDerivableR.pr (a := code κ (effBodyAt L z)) (n := y)
    (Γ := [nmemAt L (num y) (num z)]) hg hlt (by
      rw [hb]
      exact .contraction (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) H1)
  have P2 := OmegaDerivableR.npr (a := code κ (effBodyAt L z)) (n := y)
    (Γ := [memAt L (num y) (num z)]) hg hlt (by rw [hb]; exact H2)
  rw [hl] at P1 P2
  refine ⟨.contraction (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) P1, P2⟩

/-- The same, for a name at its own level, in the junk-literal calculus. -/
theorem effBody_code_derivable (z : ℕ) {κ : Lv} (hκ : lvlOf (effBody z) < κ) (y : ℕ) :
    OmegaDerivableR junkLitsR evInstR ρ (OrdinalNotation.ofNat (2 * stage z + 1) : O)
        [nmemAt (lvl z) (num y) (num z), memAt κ (num y) (num (code κ (effBody z)))] ∧
      OmegaDerivableR junkLitsR evInstR ρ (OrdinalNotation.ofNat (2 * stage z + 1) : O)
        [nmemAt κ (num y) (num (code κ (effBody z))), memAt (lvl z) (num y) (num z)] :=
  effBodyAt_code_derivable (fun _ h => Or.inr h) (lvl z) z hκ y

end Code

/-! ### The rank of the equivalence sentence -/

/-- The equivalence sentence costs at most `blkTop L` plus its complexity. -/
theorem rank_evR_effIff_le {L : Lv} (hL : 0 < L) (z : ℕ) :
    rank (evR (∀¹ effIff L z)) ≤
      Gamma0Note.nadd (Gamma0Note.blkTop L) (Gamma0Note.ofNat (∀¹ effIff L z).complexity) := by
  have h := rank_le_blkTop_lvlOf_nadd (∀¹ effIff L z)
  rw [lvlOf_all, lvlOf_effIff hL] at h
  rw [rank_evR]
  exact h

/-- **The equivalence sentence is a legitimate cut formula below `blkTop (L ⊕ 1)`.** -/
theorem rank_evR_effIff_lt {L : Lv} (hL : 0 < L) (z : ℕ) :
    rank (evR (∀¹ effIff L z)) < Gamma0Note.blkTop (Gamma0Note.nadd L 1) := by
  have h := rank_lt_blkTop_succ (∀¹ effIff L z)
  rw [lvlOf_all, lvlOf_effIff hL] at h
  rw [rank_evR]
  exact h

/-! ### Axiom audit -/

#print axioms lvlOf_rp_lt
#print axioms lvlOf_effBodyAt_lt
#print axioms lvlOf_effBody_lt
#print axioms lvlOf_effBody_of_not_good
#print axioms freeVariables_effBodyAt
#print axioms rp_derivable
#print axioms effBodyAt_derivable
#print axioms effBodyAt_numeral_derivable
#print axioms effBody_derivable
#print axioms effIff_derivable
#print axioms effBody_iff_derivable
#print axioms lvlOf_effIff
#print axioms good_code_effBodyAt
#print axioms effBodyAt_code_derivable
#print axioms effBody_code_derivable
#print axioms rank_evR_effIff_le
#print axioms rank_evR_effIff_lt

end Ramified

end OrdinalAnalysis
