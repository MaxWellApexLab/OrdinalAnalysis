/-
  The axioms of the inductive definition in the infinitary calculus of `ID₁`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §6: Proposition 6.2 (the closure axiom (F)),
  Exercise 6.3 (monotonicity of operator forms), Proposition 6.4 (the induction axiom (L)).

  **Operator forms applied to predicates.**  For the operator form `A` (the symbol `I` of
  `LXI` the place-holder), Freund writes `φ(t, θ)` for the result of applying `A` to the
  predicate `θ` at `t`.  Here the embedded form `A(t, I^{≺Ω}) = unfold A Ω t` is the base, and
  `plugI P B` replaces in `B` every atom `I^{≺Ω} s` by `P(s)` and every `¬I^{≺Ω} s` by `¬P(s)`.
  Two predicates occur: the stage `I^{≺γ}` (`predStage γ`), for which
  `plugI (I^{≺γ}) (A(t, I^{≺Ω})) = A(t, I^{≺γ})` (`plugI_unfold`), and a formula `G` with one
  free slot (`predOf G`), for which the embedded `A(x, F)` is `plugI (F⁺) (A(x, I^{≺Ω}))`
  (`embK_substI`).  Both commute with the substitutions of the calculus (`rew_plugI`).

  **Exercise 6.3** (`ex63`): if `H ⊢^α_ρ Γ, ¬θ(s), ψ(s)` for every closed `s`, then
  `H ⊢^{α ⊕ 2c}_ρ Γ, ¬φ(t, θ), φ(t, ψ)` for every closed instance `B = A(t, I^{≺Ω})`, `c` the
  complexity of `B`.  By induction on `c`; positivity (`OpShape`: no `¬I^{≺Ω}`) is what makes
  the atom case the hypothesis, and `ω ⪯ α` makes the witnesses of clause (W) admissible.

  **Proposition 6.2** (`closure_derivable`): `H ⊢^{Ω + ω·m}_0 ∀x (A(x, I) → I x)` for the
  embedded closure axiom: Lemma 6.1 for `A(n̄, I^{≺Ω})`, clause (Fix), two disjunctions and the
  ω-rule.

  **Proposition 6.4** (`indAx_derivable`): for `Cl := ∀x (A(x, ψ⁺) → ψ⁺(x))`, by induction on
  `δ ⪯ Ω` (well-founded, on the notations),

      H[δ] ⊢^{ω·β + ω·δ}_0 ¬Cl, ¬I^{≺δ} t, ψ⁺(t)        for every closed t,

  `β := Ω ⊕ c` with `c` the complexity of `ψ⁺` (so `rk ψ⁺ ⪯ β`, as Freund's
  `β = max{rk ψ⁺, 1}`, and `ω · β + ω · Ω = Ω · 2`).  The premise for `γ ≺ δ` of clause (V) on
  `¬I^{≺δ} t` combines the induction hypothesis through Exercise 6.3, Lemma 6.1 for `ψ⁺(t)`,
  clause (V) on the conjunction, the replacement of `t` by the numeral of its value, and
  clause (W) on `¬Cl`.  At `δ = Ω` the ω-rule and two disjunctions give the axiom at height
  `Ω · 2 + 5`, and the universal closure adds its number of variables.

  The sums `ω·β + ω·δ` are ordinal sums (`ThetaNote.add`), as in the source; finite
  increments are natural sums with numerals, which agree with ordinal sums
  (`add_ofNat_eq_nadd`).

  Contents.

    `predStage`, `predOf`, `plugI`, `rew_plugI`, `plugI_unfold`, `embK_substI`
    `OpShape`, `opShape_unfold`
    `ex63`                                          **Exercise 6.3**
    `closure_derivable`, `closure_axiom`            **Proposition 6.2**
    `indAx_claim`, `indAx_derivable`, `indAx_axiom` **Proposition 6.4**
-/
import OrdinalAnalysis.ID1.AxiomsPA

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting

/-! ### Predicates plugged into an operator form -/

section Plug

/-- A predicate on terms at every level. -/
abbrev Pred : Type := ∀ n : ℕ, Semiterm LIinf ℕ n → Semiformula LIinf ℕ n

/-- The stage `I^{≺γ}` as a predicate. -/
def predStage (g : Stage) : Pred := fun _ s => stageAt g s

/-- The formula `G(x)` as a predicate. -/
def predOf (G : Semiformula LIinf ℕ 1) : Pred := fun _ s => G ⇜ ![s]

/-- An atom with `I^{≺Ω}` replaced by `P`. -/
def plugRel (P : Pred) {n : ℕ} :
    {k : ℕ} → LIinf.Rel k → (Fin k → Semiterm LIinf ℕ n) → Semiformula LIinf ℕ n
  | _, Sum.inl r, v => .rel (Sum.inl r) v
  | _, Sum.inr IInfRel.X, v => .rel (Sum.inr IInfRel.X) v
  | _, Sum.inr (IInfRel.stage a), v =>
    if a = Stage.top then P n (v 0) else .rel (Sum.inr (IInfRel.stage a)) v

/-- A negated atom with `I^{≺Ω}` replaced by `P`. -/
def plugNrel (P : Pred) {n : ℕ} :
    {k : ℕ} → LIinf.Rel k → (Fin k → Semiterm LIinf ℕ n) → Semiformula LIinf ℕ n
  | _, Sum.inl r, v => .nrel (Sum.inl r) v
  | _, Sum.inr IInfRel.X, v => .nrel (Sum.inr IInfRel.X) v
  | _, Sum.inr (IInfRel.stage a), v =>
    if a = Stage.top then ∼(P n (v 0)) else .nrel (Sum.inr (IInfRel.stage a)) v

/-- **`B` with every `I^{≺Ω} s` replaced by `P(s)`**: Freund's `φ(t, θ)` from `φ(t, I^{≺Ω})`. -/
def plugI (P : Pred) : {n : ℕ} → Semiformula LIinf ℕ n → Semiformula LIinf ℕ n
  | _, .verum => ⊤
  | _, .falsum => ⊥
  | _, .rel r v => plugRel P r v
  | _, .nrel r v => plugNrel P r v
  | _, .and φ ψ => plugI P φ ⋏ plugI P ψ
  | _, .or φ ψ => plugI P φ ⋎ plugI P ψ
  | _, .all φ => ∀¹ plugI P φ
  | _, .exs φ => ∃¹ plugI P φ

variable (P : Pred)

@[simp] theorem plugI_verum {n : ℕ} : plugI P (⊤ : Semiformula LIinf ℕ n) = ⊤ := rfl

@[simp] theorem plugI_falsum {n : ℕ} : plugI P (⊥ : Semiformula LIinf ℕ n) = ⊥ := rfl

@[simp] theorem plugI_and {n : ℕ} (φ ψ : Semiformula LIinf ℕ n) :
    plugI P (φ ⋏ ψ) = plugI P φ ⋏ plugI P ψ := rfl

@[simp] theorem plugI_or {n : ℕ} (φ ψ : Semiformula LIinf ℕ n) :
    plugI P (φ ⋎ ψ) = plugI P φ ⋎ plugI P ψ := rfl

@[simp] theorem plugI_all {n : ℕ} (φ : Semiformula LIinf ℕ (n + 1)) :
    plugI P (∀¹ φ) = ∀¹ plugI P φ := rfl

@[simp] theorem plugI_exs {n : ℕ} (φ : Semiformula LIinf ℕ (n + 1)) :
    plugI P (∃¹ φ) = ∃¹ plugI P φ := rfl

theorem plugI_rel {n k : ℕ} (r : LIinf.Rel k) (v : Fin k → Semiterm LIinf ℕ n) :
    plugI P (Semiformula.rel r v) = plugRel P r v := rfl

theorem plugI_nrel {n k : ℕ} (r : LIinf.Rel k) (v : Fin k → Semiterm LIinf ℕ n) :
    plugI P (Semiformula.nrel r v) = plugNrel P r v := rfl

theorem neg_plugRel {n k : ℕ} (r : LIinf.Rel k) (v : Fin k → Semiterm LIinf ℕ n) :
    ∼(plugRel P r v) = plugNrel P r v := by
  rcases r with r | r
  · rfl
  · cases r with
    | X => rfl
    | stage a =>
      by_cases h : a = Stage.top
      · simp only [plugRel, plugNrel, if_pos h]
      · simp only [plugRel, plugNrel, if_neg h]; rfl

@[simp] theorem plugI_neg {n : ℕ} (φ : Semiformula LIinf ℕ n) :
    plugI P (∼φ) = ∼(plugI P φ) := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => exact (neg_plugRel P r v).symm
  | hnrel r v =>
    show plugRel P r v = ∼(plugNrel P r v)
    rw [← neg_plugRel]; simp
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

/-- **Plugging commutes with rewriting**, for a class `C` of rewritings closed under lifting
along which the predicates commute. -/
theorem rew_plugI (P' : Pred) (C : ∀ {n₁ n₂ : ℕ}, Rew LIinf ℕ n₁ ℕ n₂ → Prop)
    (hq : ∀ {n₁ n₂ : ℕ} {ω : Rew LIinf ℕ n₁ ℕ n₂}, C ω → C ω.q)
    (hP : ∀ {n₁ n₂ : ℕ} {ω : Rew LIinf ℕ n₁ ℕ n₂}, C ω → ∀ s, ω ▹ P n₁ s = P' n₂ (ω s)) :
    ∀ {n₁ : ℕ} (φ : Semiformula LIinf ℕ n₁) {n₂ : ℕ} {ω : Rew LIinf ℕ n₁ ℕ n₂}, C ω →
      ω ▹ plugI P φ = plugI P' (ω ▹ φ) := by
  intro n₁ φ
  induction φ using Semiformula.rec' with
  | hverum => intro n₂ ω _; simp
  | hfalsum => intro n₂ ω _; simp
  | hrel r v =>
    intro n₂ ω hω
    rw [plugI_rel, Semiformula.rew_rel, plugI_rel]
    rcases r with r | r
    · exact Semiformula.rew_rel _ _ _
    · cases r with
      | X => exact Semiformula.rew_rel _ _ _
      | stage a =>
        by_cases h : a = Stage.top
        · simp only [plugRel, if_pos h]
          exact hP hω (v 0)
        · simp only [plugRel, if_neg h]
          exact Semiformula.rew_rel _ _ _
  | hnrel r v =>
    intro n₂ ω hω
    rw [plugI_nrel, Semiformula.rew_nrel, plugI_nrel]
    rcases r with r | r
    · exact Semiformula.rew_nrel _ _ _
    · cases r with
      | X => exact Semiformula.rew_nrel _ _ _
      | stage a =>
        by_cases h : a = Stage.top
        · simp only [plugNrel, if_pos h, LogicalConnective.HomClass.map_neg]
          rw [hP hω (v 0)]
        · simp only [plugNrel, if_neg h]
          exact Semiformula.rew_nrel _ _ _
  | hand φ ψ ihφ ihψ =>
    intro n₂ ω hω
    simp only [plugI_and, LogicalConnective.HomClass.map_and, ihφ hω, ihψ hω]
  | hor φ ψ ihφ ihψ =>
    intro n₂ ω hω
    simp only [plugI_or, LogicalConnective.HomClass.map_or, ihφ hω, ihψ hω]
  | hall φ ih =>
    intro n₂ ω hω
    simp only [plugI_all, Rewriting.app_all, ih (hq hω)]
  | hexs φ ih =>
    intro n₂ ω hω
    simp only [plugI_exs, Rewriting.app_exs, ih (hq hω)]

/-- The rewritings that fix the free variables. -/
def FixF {n₁ n₂ : ℕ} (ω : Rew LIinf ℕ n₁ ℕ n₂) : Prop := ∀ x : ℕ, ω &x = &x

theorem FixF.q {n₁ n₂ : ℕ} {ω : Rew LIinf ℕ n₁ ℕ n₂} (h : FixF ω) : FixF ω.q := by
  intro x; rw [Rew.q_fvar, h x]; rfl

theorem fixF_subst {n k : ℕ} (w : Fin k → Semiterm LIinf ℕ n) : FixF (Rew.subst w) :=
  fun x => Rew.subst_fvar w x

theorem predStage_rew (g : Stage) {n₁ n₂ : ℕ} (ω : Rew LIinf ℕ n₁ ℕ n₂)
    (s : Semiterm LIinf ℕ n₁) : ω ▹ predStage g n₁ s = predStage g n₂ (ω s) :=
  Semiformula.rew_rel1 ω

theorem predOf_rew (G : Semiformula LIinf ℕ 1) {n₁ n₂ : ℕ} {ω : Rew LIinf ℕ n₁ ℕ n₂}
    (hω : FixF ω) (s : Semiterm LIinf ℕ n₁) : ω ▹ predOf G n₁ s = predOf G n₂ (ω s) := by
  show ω ▹ (G ⇜ ![s]) = G ⇜ ![ω s]
  simpa [← comp_app] using smul_ext' (φ := G) <| by
    ext x
    · obtain rfl := Subsingleton.elim x 0; simp [Rew.comp_app]
    · simp [Rew.comp_app, hω x]

/-- Plugging a stage commutes with the substitutions of the calculus. -/
theorem rew_plugI_stage (g : Stage) {n₁ n₂ : ℕ} {ω : Rew LIinf ℕ n₁ ℕ n₂} (hω : FixF ω)
    (φ : Semiformula LIinf ℕ n₁) : ω ▹ plugI (predStage g) φ = plugI (predStage g) (ω ▹ φ) :=
  rew_plugI (predStage g) (predStage g) FixF (fun h => h.q)
    (fun {_ _} {ω} _ s => predStage_rew g ω s) φ hω

theorem rew_plugI_of (G : Semiformula LIinf ℕ 1) {n₁ n₂ : ℕ} {ω : Rew LIinf ℕ n₁ ℕ n₂}
    (hω : FixF ω) (φ : Semiformula LIinf ℕ n₁) :
    ω ▹ plugI (predOf G) φ = plugI (predOf G) (ω ▹ φ) :=
  rew_plugI (predOf G) (predOf G) FixF (fun h => h.q) (fun h s => predOf_rew G h s) φ hω

/-- The rewritings that send every free variable `x` to the numeral of `f x`. -/
def NumF (f : ℕ → ℕ) {n₁ n₂ : ℕ} (ω : Rew LIinf ℕ n₁ ℕ n₂) : Prop :=
  ∀ x : ℕ, ω &x = ((f x : ℕ) : Semiterm LIinf ℕ n₂)

theorem NumF.q {f : ℕ → ℕ} {n₁ n₂ : ℕ} {ω : Rew LIinf ℕ n₁ ℕ n₂} (h : NumF f ω) :
    NumF f ω.q := by
  intro x; rw [Rew.q_fvar, h x]; simp

theorem predOf_numF (f : ℕ → ℕ) (G : Semiformula LIinf ℕ 1) {n₁ n₂ : ℕ}
    {ω : Rew LIinf ℕ n₁ ℕ n₂} (hω : NumF f ω) (s : Semiterm LIinf ℕ n₁) :
    ω ▹ predOf G n₁ s = predOf (numSubst₁ f ▹ G) n₂ (ω s) := by
  show ω ▹ (G ⇜ ![s]) = (numSubst₁ f ▹ G) ⇜ ![ω s]
  simpa [← comp_app] using smul_ext' (φ := G) <| by
    ext x
    · obtain rfl := Subsingleton.elim x 0; simp [Rew.comp_app]
    · simp [Rew.comp_app, hω x, numSubst₁]

theorem numF_numSubst₁ (f : ℕ → ℕ) : NumF f (numSubst₁ f) := fun _ => rfl

theorem rew_plugI_num (f : ℕ → ℕ) (G : Semiformula LIinf ℕ 1) (φ : Semiformula LIinf ℕ 1) :
    numSubst₁ f ▹ plugI (predOf G) φ = plugI (predOf (numSubst₁ f ▹ G)) (numSubst₁ f ▹ φ) :=
  rew_plugI (predOf G) (predOf (numSubst₁ f ▹ G)) (NumF f) (fun h => h.q)
    (fun h s => predOf_numF f G h s) φ (numF_numSubst₁ f)

end Plug

/-! ### The two plugged forms -/

section PlugForms

theorem plugI_lMap_top (g : Stage) :
    ∀ {n : ℕ} (φ : Semiformula LXI ℕ n),
      plugI (predStage g) (Semiformula.lMap (stageHom Stage.top) φ) =
        Semiformula.lMap (stageHom g) φ := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v =>
    rw [Semiformula.lMap_rel, Semiformula.lMap_rel, plugI_rel]
    rcases r with r | r
    · show Semiformula.rel _ _ = Semiformula.rel _ _
      congr 1
      funext i
      exact lMap_stageHom_term _ _ (v i)
    · cases r with
      | X =>
        show Semiformula.rel _ _ = Semiformula.rel _ _
        congr 1
        funext i
        exact lMap_stageHom_term _ _ (v i)
      | I =>
        show plugRel (predStage g) (Sum.inr (IInfRel.stage Stage.top)) _ = _
        simp only [plugRel]
        show stageAt g _ = Semiformula.rel (Sum.inr (IInfRel.stage g)) _
        rw [rel_eq_vec (Sum.inr (IInfRel.stage g))]
        show Semiformula.rel _ _ = Semiformula.rel _ _
        congr 1
        funext i
        obtain rfl := Subsingleton.elim i 0
        exact lMap_stageHom_term _ _ (v 0)
  | hnrel r v =>
    rw [Semiformula.lMap_nrel, Semiformula.lMap_nrel, plugI_nrel]
    rcases r with r | r
    · show Semiformula.nrel _ _ = Semiformula.nrel _ _
      congr 1
      funext i
      exact lMap_stageHom_term _ _ (v i)
    · cases r with
      | X =>
        show Semiformula.nrel _ _ = Semiformula.nrel _ _
        congr 1
        funext i
        exact lMap_stageHom_term _ _ (v i)
      | I =>
        show plugNrel (predStage g) (Sum.inr (IInfRel.stage Stage.top)) _ = _
        simp only [plugNrel]
        show nstageAt g _ = Semiformula.nrel (Sum.inr (IInfRel.stage g)) _
        rw [nrel_eq_vec (Sum.inr (IInfRel.stage g))]
        show Semiformula.nrel _ _ = Semiformula.nrel _ _
        congr 1
        funext i
        obtain rfl := Subsingleton.elim i 0
        exact lMap_stageHom_term _ _ (v 0)
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and, plugI_and, ihφ,
      ihψ]
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or, plugI_or, ihφ, ihψ]
  | hall φ ih => rw [Semiformula.lMap_all, Semiformula.lMap_all, plugI_all, ih]
  | hexs φ ih => rw [Semiformula.lMap_exs, Semiformula.lMap_exs, plugI_exs, ih]

theorem unfold_eq_rew (A : Semisentence LXI 1) (a : Stage) (t : SyntacticTerm LIinf) :
    unfold A a t =
      Rew.subst ![t] ▹ Semiformula.lMap (stageHom a) (Rewriting.emb A : Semiformula LXI ℕ 1) := by
  rw [unfold, formAt, Semiformula.lMap_emb]

/-- **`φ(t, I^{≺γ})` is `φ(t, I^{≺Ω})` with the stage `I^{≺γ}` plugged in.** -/
theorem plugI_unfold (A : Semisentence LXI 1) (g : Stage) (t : SyntacticTerm LIinf) :
    plugI (predStage g) (unfold A Stage.top t) = unfold A g t := by
  rw [unfold_eq_rew, unfold_eq_rew, ← rew_plugI_stage g (fixF_subst _), plugI_lMap_top]

/-- **The embedded `A(x, F)` is `A(x, I^{≺Ω})` with `F⁺` plugged in.** -/
theorem embK_substI (F : Semiformula LXI ℕ 1) :
    ∀ {n : ℕ} (φ : Semiformula LXI ℕ n),
      embK (substI F φ) = plugI (predOf (embK F)) (embK φ) := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
    rcases r with r | r
    · rfl
    · cases r with
      | X => rfl
      | I =>
        show embK (F/[v 0]) = plugRel _ (Sum.inr (IInfRel.stage Stage.top)) (embT ∘ v)
        rw [embK_subst₁]
        simp only [plugRel]
        rfl
  | hnrel r v =>
    rcases r with r | r
    · rfl
    · cases r with
      | X => rfl
      | I =>
        show embK (∼(F/[v 0])) = plugNrel _ (Sum.inr (IInfRel.stage Stage.top)) (embT ∘ v)
        rw [embK_neg, embK_subst₁]
        simp only [plugNrel]
        rfl
  | hand φ ψ ihφ ihψ =>
    show embK (substI F φ ⋏ substI F ψ) = _
    rw [embK_and, embK_and, plugI_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
    show embK (substI F φ ⋎ substI F ψ) = _
    rw [embK_or, embK_or, plugI_or, ihφ, ihψ]
  | hall φ ih =>
    show embK (∀¹ substI F φ) = _
    rw [embK_all, embK_all, plugI_all, ih]
  | hexs φ ih =>
    show embK (∃¹ substI F φ) = _
    rw [embK_exs, embK_exs, plugI_exs, ih]

/-- The atoms of an embedded positive, `X`-free operator form: arithmetic atoms, positive
atoms `I^{≺Ω} s`, and negated arithmetic atoms. -/
def OpRel : {k : ℕ} → LIinf.Rel k → Prop
  | _, Sum.inl _ => True
  | _, Sum.inr IInfRel.X => False
  | _, Sum.inr (IInfRel.stage a) => a = Stage.top

/-- Negated atoms of an embedded positive form are arithmetic. -/
def OpNrel : {k : ℕ} → LIinf.Rel k → Prop
  | _, Sum.inl _ => True
  | _, Sum.inr _ => False

/-- **The shape of `A(t, I^{≺Ω})`** for a positive, `X`-free operator form. -/
def OpShape {ξ : Type*} : {n : ℕ} → Semiformula LIinf ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel r _ => OpRel r
  | _, .nrel r _ => OpNrel r
  | _, .and φ ψ => OpShape φ ∧ OpShape ψ
  | _, .or φ ψ => OpShape φ ∧ OpShape ψ
  | _, .all φ => OpShape φ
  | _, .exs φ => OpShape φ

theorem opShape_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LIinf ξ₁ n₁ ξ₂ n₂)
    {φ : Semiformula LIinf ξ₁ n₁} (h : OpShape φ) : OpShape (ω ▹ φ) := by
  revert h
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => intro _; simp only [LogicalConnective.HomClass.map_top]; trivial
  | hfalsum => intro _; simp only [LogicalConnective.HomClass.map_bot]; trivial
  | hrel r v => intro h; rw [Semiformula.rew_rel]; exact h
  | hnrel r v => intro h; rw [Semiformula.rew_nrel]; exact h
  | hand φ ψ ihφ ihψ =>
    intro h; rw [LogicalConnective.HomClass.map_and]; exact ⟨ihφ ω h.1, ihψ ω h.2⟩
  | hor φ ψ ihφ ihψ =>
    intro h; rw [LogicalConnective.HomClass.map_or]; exact ⟨ihφ ω h.1, ihψ ω h.2⟩
  | hall φ ih => intro h; rw [Rewriting.app_all]; exact ih ω.q h
  | hexs φ ih => intro h; rw [Rewriting.app_exs]; exact ih ω.q h

theorem opShape_lMap_top {ξ : Type*} :
    ∀ {n : ℕ} (φ : Semiformula LXI ξ n), Positive φ → XFreeL φ →
      OpShape (Semiformula.lMap (stageHom Stage.top) φ)
  | _, .verum, _, _ => trivial
  | _, .falsum, _, _ => trivial
  | _, .rel (Sum.inl _) _, _, _ => trivial
  | _, .rel (Sum.inr IXRel.X) _, _, h => h.elim
  | _, .rel (Sum.inr IXRel.I) _, _, _ => rfl
  | _, .nrel (Sum.inl _) _, _, _ => trivial
  | _, .nrel (Sum.inr IXRel.X) _, _, h => h.elim
  | _, .nrel (Sum.inr IXRel.I) _, h, _ => h.elim
  | _, .and φ ψ, hp, hx => ⟨opShape_lMap_top φ hp.1 hx.1, opShape_lMap_top ψ hp.2 hx.2⟩
  | _, .or φ ψ, hp, hx => ⟨opShape_lMap_top φ hp.1 hx.1, opShape_lMap_top ψ hp.2 hx.2⟩
  | _, .all φ, hp, hx => opShape_lMap_top φ hp hx
  | _, .exs φ, hp, hx => opShape_lMap_top φ hp hx

/-- The embedded operator form `A(t, I^{≺Ω})` of a positive `X`-free `A` has the shape
Exercise 6.3 needs. -/
theorem opShape_unfold {A : Semisentence LXI 1} (hA : Positive A) (hX : XFreeL A)
    (t : SyntacticTerm LIinf) : OpShape (unfold A Stage.top t) :=
  opShape_rew _ (opShape_rew _ (opShape_lMap_top A hA hX))

variable (P : Pred)

theorem params_plugI {S : Set ThetaNote} (hP : ∀ (n : ℕ) (s : Semiterm LIinf ℕ n), params (P n s) ⊆ S) :
    ∀ {n : ℕ} (φ : Semiformula LIinf ℕ n), params (plugI P φ) ⊆ params φ ∪ S := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => exact Set.empty_subset _
  | hfalsum => exact Set.empty_subset _
  | hrel r v =>
    rw [plugI_rel]
    rcases r with r | r
    · exact Set.subset_union_left
    · cases r with
      | X => exact Set.subset_union_left
      | stage a =>
        by_cases h : a = Stage.top
        · simp only [plugRel, if_pos h]; exact (hP _ _).trans Set.subset_union_right
        · simp only [plugRel, if_neg h]; exact Set.subset_union_left
  | hnrel r v =>
    rw [plugI_nrel]
    rcases r with r | r
    · exact Set.subset_union_left
    · cases r with
      | X => exact Set.subset_union_left
      | stage a =>
        by_cases h : a = Stage.top
        · simp only [plugNrel, if_pos h, params_neg]
          exact (hP _ _).trans Set.subset_union_right
        · simp only [plugNrel, if_neg h]; exact Set.subset_union_left
  | hand φ ψ ihφ ihψ =>
    rw [plugI_and, params_and, params_and]
    exact Set.union_subset (ihφ.trans (Set.union_subset_union_left _ Set.subset_union_left))
      (ihψ.trans (Set.union_subset_union_left _ Set.subset_union_right))
  | hor φ ψ ihφ ihψ =>
    rw [plugI_or, params_or, params_or]
    exact Set.union_subset (ihφ.trans (Set.union_subset_union_left _ Set.subset_union_left))
      (ihψ.trans (Set.union_subset_union_left _ Set.subset_union_right))
  | hall φ ih => rw [plugI_all, params_all, params_all]; exact ih
  | hexs φ ih => rw [plugI_exs, params_exs, params_exs]; exact ih

theorem xFreeI_plugI (hP : ∀ (n : ℕ) (s : Semiterm LIinf ℕ n), XFreeI (P n s)) :
    ∀ {n : ℕ} (φ : Semiformula LIinf ℕ n), XFreeI φ → XFreeI (plugI P φ) := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro _; trivial
  | hfalsum => intro _; trivial
  | hrel r v =>
    intro h
    rw [plugI_rel]
    rcases r with r | r
    · exact h
    · cases r with
      | X => exact h
      | stage a =>
        by_cases ha : a = Stage.top
        · simp only [plugRel, if_pos ha]; exact hP _ _
        · simp only [plugRel, if_neg ha]; exact h
  | hnrel r v =>
    intro h
    rw [plugI_nrel]
    rcases r with r | r
    · exact h
    · cases r with
      | X => exact h
      | stage a =>
        by_cases ha : a = Stage.top
        · simp only [plugNrel, if_pos ha]; exact (xFreeI_neg _).mpr (hP _ _)
        · simp only [plugNrel, if_neg ha]; exact h
  | hand φ ψ ihφ ihψ => intro h; exact ⟨ihφ h.1, ihψ h.2⟩
  | hor φ ψ ihφ ihψ => intro h; exact ⟨ihφ h.1, ihψ h.2⟩
  | hall φ ih => intro h; exact ih h
  | hexs φ ih => intro h; exact ih h

theorem freeVariables_plugI
    (hP : ∀ (n : ℕ) (s : Semiterm LIinf ℕ n), s.freeVariables = ∅ → (P n s).freeVariables = ∅) :
    ∀ {n : ℕ} (φ : Semiformula LIinf ℕ n), φ.freeVariables = ∅ →
      (plugI P φ).freeVariables = ∅ := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro _; rfl
  | hfalsum => intro _; rfl
  | hrel r v =>
    intro h
    rw [plugI_rel]
    rcases r with r | r
    · exact h
    · cases r with
      | X => exact h
      | stage a =>
        by_cases ha : a = Stage.top
        · simp only [plugRel, if_pos ha]; exact hP _ _ (freeVariables_rel_arg h 0)
        · simp only [plugRel, if_neg ha]; exact h
  | hnrel r v =>
    intro h
    rw [plugI_nrel]
    rcases r with r | r
    · exact h
    · cases r with
      | X => exact h
      | stage a =>
        by_cases ha : a = Stage.top
        · simp only [plugNrel, if_pos ha, Semiformula.freeVariables_not]
          exact hP _ _ (freeVariables_nrel_arg h 0)
        · simp only [plugNrel, if_neg ha]; exact h
  | hand φ ψ ihφ ihψ =>
    intro h
    rw [Semiformula.freeVariables_and, Finset.union_eq_empty] at h
    rw [plugI_and, Semiformula.freeVariables_and, ihφ h.1, ihψ h.2, Finset.union_empty]
  | hor φ ψ ihφ ihψ =>
    intro h
    rw [Semiformula.freeVariables_or, Finset.union_eq_empty] at h
    rw [plugI_or, Semiformula.freeVariables_or, ihφ h.1, ihψ h.2, Finset.union_empty]
  | hall φ ih => intro h; rw [plugI_all, Semiformula.freeVariables_all]; exact ih h
  | hexs φ ih => intro h; rw [plugI_exs, Semiformula.freeVariables_exs]; exact ih h

theorem params_predStage (g : Stage) (n : ℕ) (s : Semiterm LIinf ℕ n) :
    params (predStage g n s) ⊆ {g.1} := subset_refl _

theorem params_predOf (G : Semiformula LIinf ℕ 1) (n : ℕ) (s : Semiterm LIinf ℕ n) :
    params (predOf G n s) ⊆ params G := by
  show params (Rew.subst ![s] ▹ G) ⊆ _; rw [params_rew]

theorem xFreeI_predStage (g : Stage) (n : ℕ) (s : Semiterm LIinf ℕ n) :
    XFreeI (predStage g n s) := fun h => h

theorem xFreeI_predOf {G : Semiformula LIinf ℕ 1} (hG : XFreeI G) (n : ℕ)
    (s : Semiterm LIinf ℕ n) : XFreeI (predOf G n s) := (xFreeI_rew _ _).mpr hG

theorem freeVariables_predOf {G : Semiformula LIinf ℕ 1} (hG : G.freeVariables = ∅) (n : ℕ)
    (s : Semiterm LIinf ℕ n) (hs : s.freeVariables = ∅) : (predOf G n s).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![s]) (φ := G) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ ((Rew.subst ![s]) #i : Semiterm LIinf ℕ n).freeVariables := hi
    obtain rfl := Subsingleton.elim i 0
    simp only [Rew.subst_bvar, Matrix.cons_val_zero, hs] at hi'
    exact Finset.notMem_empty x hi'
  · have hz' : z ∈ G.freeVariables := hz
    rw [hG] at hz'
    exact Finset.notMem_empty z hz'

end PlugForms

/-! ### Exercise 6.3 -/

section Ex63

variable {A : Semisentence LXI 1} {ρ : ThetaNote} {H : Set ThetaNote → Set ThetaNote}

theorem plugI_subst_numI (P : Pred) (hP : ∀ {n₁ n₂ : ℕ} {ω : Rew LIinf ℕ n₁ ℕ n₂}, FixF ω →
      ∀ s, ω ▹ P n₁ s = P n₂ (ω s)) (φ : Semiformula LIinf ℕ 1) (n : ℕ) :
    (plugI P φ)/[numI n] = plugI P (φ/[numI n]) :=
  rew_plugI P P FixF (fun h => h.q) hP φ (fixF_subst _)

/-- **Freund, Exercise 6.3** (monotonicity of positive operator forms): if
`H ⊢^α_ρ Γ, ¬I^{≺γ}(s), G(s)` for every closed term `s`, then
`H ⊢^{α ⊕ 2c}_ρ Γ, ¬B(I^{≺γ}), B(G)` for every closed `B` of the shape of `A(t, I^{≺Ω})`
(`OpShape`) of complexity at most `c`, where `B(P)` plugs `P` in for `I^{≺Ω}`. -/
theorem ex63 (hH : ThetaNote.Nice H) (g : Stage) (G : Semiformula LIinf ℕ 1) {α : ThetaNote}
    (hω : omegaT ≤ α) (hα : α ∈ H ∅) (Γ : Sequent LIinf) (hΓ : paramsList Γ ⊆ H ∅)
    (hg : g.1 ∈ H ∅) (hG : params G ⊆ H ∅)
    (hyp : ∀ u : SyntacticTerm LIinf, u.freeVariables = ∅ →
      IDerivable A ρ H α (∼(stageAt g u) :: G/[u] :: Γ)) :
    ∀ (c : ℕ) (B : Proposition LIinf), B.complexity ≤ c → OpShape B → B.freeVariables = ∅ →
      params B ⊆ H ∅ →
      IDerivable A ρ H (ThetaNote.nadd α (ThetaNote.ofNat (2 * c)))
        (∼(plugI (predStage g) B) :: plugI (predOf G) B :: Γ) := by
  have hθ : ∀ {m : ℕ} (χ : Semiformula LIinf ℕ m), params χ ⊆ H ∅ →
      params (plugI (predStage g) χ) ⊆ H ∅ := fun χ h =>
    (params_plugI (predStage g) (params_predStage g) χ).trans
      (Set.union_subset h (Set.singleton_subset_iff.mpr hg))
  have hψ : ∀ {m : ℕ} (χ : Semiformula LIinf ℕ m), params χ ⊆ H ∅ →
      params (plugI (predOf G) χ) ⊆ H ∅ := fun χ h =>
    (params_plugI (predOf G) (params_predOf G) χ).trans (Set.union_subset h hG)
  have hmem : ∀ k : ℕ, ThetaNote.nadd α (ThetaNote.ofNat k) ∈ H ∅ := fun k =>
    hH.nadd_mem hα (hH.ofNat_mem k)
  have hone : ∀ k, ThetaNote.one < ThetaNote.nadd α (ThetaNote.ofNat k) := fun k =>
    lt_of_lt_of_le (by rw [← ThetaNote.ofNat_one]; exact ThetaNote.ofNat_lt_omega 1)
      (le_trans hω (ThetaNote.le_nadd_left _ _))
  have hnum : ∀ (n k : ℕ), ThetaNote.ofNat n < ThetaNote.nadd α (ThetaNote.ofNat k) := fun n k =>
    lt_of_lt_of_le (ThetaNote.ofNat_lt_omega n) (le_trans hω (ThetaNote.le_nadd_left _ _))
  have hlt : ∀ j k : ℕ, j < k → ThetaNote.nadd α (ThetaNote.ofNat j) <
      ThetaNote.nadd α (ThetaNote.ofNat k) := fun j k h => ThetaNote.nadd_ofNat_lt_nadd_ofNat _ h
  have hΘ := plugI_subst_numI (predStage g) (fun {_ _} {ω} _ s => predStage_rew g ω s)
  have hΨ := plugI_subst_numI (predOf G) (fun h s => predOf_rew G h s)
  have pl : ∀ Δ : Sequent LIinf, (∀ χ ∈ Δ, params χ ⊆ H ∅) → paramsList Δ ⊆ H ∅ := by
    intro Δ h x ⟨χ, hχ, hx⟩; exact h χ hχ hx
  have plΓ : ∀ χ ∈ Γ, params χ ⊆ H ∅ := fun χ hχ => params_subset_paramsList hχ |>.trans hΓ
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro B hc hS hf hp
  -- the sequent and its parameters
  have pseq : ∀ χ ∈ (∼(plugI (predStage g) B) :: plugI (predOf G) B :: Γ), params χ ⊆ H ∅ := by
    intro χ hχ
    simp only [List.mem_cons] at hχ
    rcases hχ with rfl | rfl | hχ
    · rw [params_neg]; exact hθ B hp
    · exact hψ B hp
    · exact plΓ χ hχ
  have hP := pl _ pseq
  revert hc hS hf hp pseq hP
  cases B using cases0 with
  | hverum =>
    intro _ _ _ _ _ hP
    exact .verum (hmem _) hP (List.mem_cons_of_mem _ List.mem_cons_self)
  | hfalsum =>
    intro _ _ _ _ _ hP
    exact .verum (hmem _) hP List.mem_cons_self
  | hrel k r v =>
    intro _ hS hf _ _ hP
    rcases r with r | r
    · -- an arithmetic literal: one of the two is true
      have hl : IsArithLit (Semiformula.rel (Sum.inl r : LIinf.Rel k) v) :=
        ⟨k, r, v, Or.inl rfl, freeVariables_rel_arg hf⟩
      by_cases ht : TrueN (Semiformula.rel (Sum.inl r : LIinf.Rel k) v)
      · exact .literal (hmem _) hP ⟨hl, ht⟩ (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact .literal (hmem _) hP ⟨hl.neg, (trueN_neg _).mpr ht⟩ List.mem_cons_self
    · cases r with
      | X => exact hS.elim
      | stage a =>
        obtain rfl : a = Stage.top := hS
        -- the atom `I^{≺Ω} s`: the hypothesis at `s`
        have e1 : plugI (predStage g) (Semiformula.rel (Sum.inr (IInfRel.stage Stage.top)) v) =
            stageAt g (v 0) := rfl
        have e2 : plugI (predOf G) (Semiformula.rel (Sum.inr (IInfRel.stage Stage.top)) v) =
            G/[v 0] := rfl
        rw [e1, e2]
        exact (hyp (v 0) (freeVariables_rel_arg hf 0)).mono_height (ThetaNote.le_nadd_left _ _)
          (hmem _)
  | hnrel k r v =>
    intro _ hS hf _ _ hP
    rcases r with r | r
    · have hl : IsArithLit (Semiformula.nrel (Sum.inl r : LIinf.Rel k) v) :=
        ⟨k, r, v, Or.inr rfl, freeVariables_nrel_arg hf⟩
      by_cases ht : TrueN (Semiformula.nrel (Sum.inl r : LIinf.Rel k) v)
      · exact .literal (hmem _) hP ⟨hl, ht⟩ (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact .literal (hmem _) hP ⟨hl.neg, (trueN_neg _).mpr ht⟩ List.mem_cons_self
    · exact hS.elim
  | hand B₀ B₁ =>
    intro hc hS hf hp pseq hP
    rw [Semiformula.complexity_and] at hc
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [Semiformula.freeVariables_and, Finset.union_eq_empty] at hf
    rw [params_and] at hp
    have hp0 : params B₀ ⊆ H ∅ := Set.subset_union_left.trans hp
    have hp1 : params B₁ ⊆ H ∅ := Set.subset_union_right.trans hp
    set X₀ := plugI (predStage g) B₀
    set X₁ := plugI (predStage g) B₁
    set Y₀ := plugI (predOf G) B₀
    set Y₁ := plugI (predOf G) B₁
    have eX : ∼(plugI (predStage g) (B₀ ⋏ B₁)) = ∼X₀ ⋎ ∼X₁ := by simp [X₀, X₁]
    have eY : plugI (predOf G) (B₀ ⋏ B₁) = Y₀ ⋏ Y₁ := rfl
    rw [eX, eY] at hP ⊢
    have step : ∀ (Xi Yi : Proposition LIinf), params Xi ⊆ H ∅ → params Yi ⊆ H ∅ →
        IDerivable A ρ H (ThetaNote.nadd α (ThetaNote.ofNat (2 * c'))) (∼Xi :: Yi :: Γ) →
        IDerivable A ρ H (ThetaNote.nadd α (ThetaNote.ofNat (2 * c')))
          (∼Xi :: Yi :: (∼X₀ ⋎ ∼X₁) :: (Y₀ ⋏ Y₁) :: Γ) := by
      intro Xi Yi hXi hYi d
      refine d.weaken_seq hH.isOperator (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        tauto) (pl _ ?_)
      intro χ hχ
      simp only [List.mem_cons] at hχ
      rcases hχ with rfl | rfl | rfl | rfl | hχ
      · rw [params_neg]; exact hXi
      · exact hYi
      · rw [params_or, params_neg, params_neg]; exact Set.union_subset (hθ B₀ hp0) (hθ B₁ hp1)
      · rw [params_and]; exact Set.union_subset (hψ B₀ hp0) (hψ B₁ hp1)
      · exact plΓ χ hχ
    have d0 := step X₀ Y₀ (hθ B₀ hp0) (hψ B₀ hp0)
      (ih c' (by omega) B₀ (by omega) hS.1 hf.1 hp0)
    have d1 := step X₁ Y₁ (hθ B₁ hp1) (hψ B₁ hp1)
      (ih c' (by omega) B₁ (by omega) hS.2 hf.2 hp1)
    have pY : ∀ Yi, params Yi ⊆ H ∅ →
        paramsList (Yi :: (∼X₀ ⋎ ∼X₁) :: (Y₀ ⋏ Y₁) :: Γ) ⊆ H ∅ := by
      intro Yi hYi
      rw [paramsList_cons]; exact Set.union_subset hYi hP
    have e0 : IDerivable A ρ H (ThetaNote.nadd α (ThetaNote.ofNat (2 * c' + 1)))
        (Y₀ :: (∼X₀ ⋎ ∼X₁) :: (Y₀ ⋏ Y₁) :: Γ) :=
      .orL (hmem _) (pY Y₀ (hψ B₀ hp0)) (List.mem_cons_of_mem _ List.mem_cons_self)
        (hlt _ _ (by omega)) d0
    have e1 : IDerivable A ρ H (ThetaNote.nadd α (ThetaNote.ofNat (2 * c' + 1)))
        (Y₁ :: (∼X₀ ⋎ ∼X₁) :: (Y₀ ⋏ Y₁) :: Γ) :=
      .orR (hmem _) (pY Y₁ (hψ B₁ hp1)) (List.mem_cons_of_mem _ List.mem_cons_self) (hone _)
        (hlt _ _ (by omega)) d1
    exact .and (hmem _) hP (List.mem_cons_of_mem _ List.mem_cons_self) (hlt _ _ (by omega))
      (hlt _ _ (by omega)) e0 e1
  | hor B₀ B₁ =>
    intro hc hS hf hp pseq hP
    rw [Semiformula.complexity_or] at hc
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [Semiformula.freeVariables_or, Finset.union_eq_empty] at hf
    rw [params_or] at hp
    have hp0 : params B₀ ⊆ H ∅ := Set.subset_union_left.trans hp
    have hp1 : params B₁ ⊆ H ∅ := Set.subset_union_right.trans hp
    set X₀ := plugI (predStage g) B₀
    set X₁ := plugI (predStage g) B₁
    set Y₀ := plugI (predOf G) B₀
    set Y₁ := plugI (predOf G) B₁
    have eX : ∼(plugI (predStage g) (B₀ ⋎ B₁)) = ∼X₀ ⋏ ∼X₁ := by simp [X₀, X₁]
    have eY : plugI (predOf G) (B₀ ⋎ B₁) = Y₀ ⋎ Y₁ := rfl
    rw [eX, eY] at hP ⊢
    have step : ∀ (Xi Yi : Proposition LIinf), params Xi ⊆ H ∅ → params Yi ⊆ H ∅ →
        IDerivable A ρ H (ThetaNote.nadd α (ThetaNote.ofNat (2 * c'))) (∼Xi :: Yi :: Γ) →
        IDerivable A ρ H (ThetaNote.nadd α (ThetaNote.ofNat (2 * c')))
          (Yi :: ∼Xi :: (∼X₀ ⋏ ∼X₁) :: (Y₀ ⋎ Y₁) :: Γ) := by
      intro Xi Yi hXi hYi d
      refine d.weaken_seq hH.isOperator (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        tauto) (pl _ ?_)
      intro χ hχ
      simp only [List.mem_cons] at hχ
      rcases hχ with rfl | rfl | rfl | rfl | hχ
      · exact hYi
      · rw [params_neg]; exact hXi
      · rw [params_and, params_neg, params_neg]; exact Set.union_subset (hθ B₀ hp0) (hθ B₁ hp1)
      · rw [params_or]; exact Set.union_subset (hψ B₀ hp0) (hψ B₁ hp1)
      · exact plΓ χ hχ
    have d0 := step X₀ Y₀ (hθ B₀ hp0) (hψ B₀ hp0) (ih c' (by omega) B₀ (by omega) hS.1 hf.1 hp0)
    have d1 := step X₁ Y₁ (hθ B₁ hp1) (hψ B₁ hp1) (ih c' (by omega) B₁ (by omega) hS.2 hf.2 hp1)
    have pX : ∀ Xi, params Xi ⊆ H ∅ →
        paramsList (∼Xi :: (∼X₀ ⋏ ∼X₁) :: (Y₀ ⋎ Y₁) :: Γ) ⊆ H ∅ := by
      intro Xi hXi
      rw [paramsList_cons, params_neg]; exact Set.union_subset hXi hP
    have e0 : IDerivable A ρ H (ThetaNote.nadd α (ThetaNote.ofNat (2 * c' + 1)))
        (∼X₀ :: (∼X₀ ⋏ ∼X₁) :: (Y₀ ⋎ Y₁) :: Γ) :=
      .orL (hmem _) (pX X₀ (hθ B₀ hp0))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (hlt _ _ (by omega)) d0
    have e1 : IDerivable A ρ H (ThetaNote.nadd α (ThetaNote.ofNat (2 * c' + 1)))
        (∼X₁ :: (∼X₀ ⋏ ∼X₁) :: (Y₀ ⋎ Y₁) :: Γ) :=
      .orR (hmem _) (pX X₁ (hθ B₁ hp1))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (hone _)
        (hlt _ _ (by omega)) d1
    exact .and (hmem _) hP List.mem_cons_self (hlt _ _ (by omega)) (hlt _ _ (by omega)) e0 e1
  | hall φ =>
    intro hc hS hf hp pseq hP
    rw [Semiformula.complexity_all] at hc
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [Semiformula.freeVariables_all] at hf
    rw [params_all] at hp
    have eX : ∼(plugI (predStage g) (∀¹ φ)) = ∃¹ (∼plugI (predStage g) φ) := by simp
    have eY : plugI (predOf G) (∀¹ φ) = ∀¹ plugI (predOf G) φ := rfl
    rw [eX, eY] at hP ⊢
    refine .all (fun _ => ThetaNote.nadd α (ThetaNote.ofNat (2 * c' + 1))) (hmem _) hP
      (List.mem_cons_of_mem _ List.mem_cons_self) (fun _ => hlt (2 * c' + 1) (2 * (c' + 1)) (by omega)) (fun n => ?_)
    have hpn : params (φ/[numI n]) ⊆ H ∅ := by rw [params_subst]; exact hp
    have d := ih c' (by omega) (φ/[numI n]) (by rw [Semiformula.complexity_rew]; omega)
      (opShape_rew _ hS) (freeVariables_subst_numI φ hf n) hpn
    rw [← hΘ, ← hΨ] at d
    have hneg : (∼plugI (predStage g) φ)/[numI n] = ∼((plugI (predStage g) φ)/[numI n]) := by
      simp
    refine .exs (α₀ := ThetaNote.nadd α (ThetaNote.ofNat (2 * c'))) n (hmem _) ?_
      (List.mem_cons_of_mem _ List.mem_cons_self) (hnum _ _) (hlt (2 * c') (2 * c' + 1) (by omega)) ?_
    · rw [paramsList_cons, params_subst]
      exact Set.union_subset (hψ φ hp) hP
    · rw [hneg]
      refine d.weaken_seq hH.isOperator (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        tauto) ?_
      rw [paramsList_cons, paramsList_cons, params_neg, params_subst, params_subst]
      exact Set.union_subset (hθ φ hp) (Set.union_subset (hψ φ hp) hP)
  | hexs φ =>
    intro hc hS hf hp pseq hP
    rw [Semiformula.complexity_exs] at hc
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [Semiformula.freeVariables_exs] at hf
    rw [params_exs] at hp
    have eX : ∼(plugI (predStage g) (∃¹ φ)) = ∀¹ (∼plugI (predStage g) φ) := by simp
    have eY : plugI (predOf G) (∃¹ φ) = ∃¹ plugI (predOf G) φ := rfl
    rw [eX, eY] at hP ⊢
    refine .all (fun _ => ThetaNote.nadd α (ThetaNote.ofNat (2 * c' + 1))) (hmem _) hP
      List.mem_cons_self (fun _ => hlt (2 * c' + 1) (2 * (c' + 1)) (by omega)) (fun n => ?_)
    have hpn : params (φ/[numI n]) ⊆ H ∅ := by rw [params_subst]; exact hp
    have d := ih c' (by omega) (φ/[numI n]) (by rw [Semiformula.complexity_rew]; omega)
      (opShape_rew _ hS) (freeVariables_subst_numI φ hf n) hpn
    rw [← hΘ, ← hΨ] at d
    have hneg : (∼plugI (predStage g) φ)/[numI n] = ∼((plugI (predStage g) φ)/[numI n]) := by
      simp
    rw [hneg]
    refine .exs (α₀ := ThetaNote.nadd α (ThetaNote.ofNat (2 * c'))) n (hmem _) ?_
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (hnum _ _) (hlt (2 * c') (2 * c' + 1) (by omega)) ?_
    · rw [paramsList_cons, params_neg, params_subst]
      exact Set.union_subset (hθ φ hp) hP
    · refine d.weaken_seq hH.isOperator (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        tauto) ?_
      rw [paramsList_cons, paramsList_cons, params_neg, params_subst, params_subst]
      exact Set.union_subset (hψ φ hp) (Set.union_subset (hθ φ hp) hP)

end Ex63

/-! ### Proposition 6.2: the closure axiom -/

section Closure

variable {A : Semisentence LXI 1}

/-- The body `A(x, I^{≺Ω})` of the embedded operator form, with the slot `x` free. -/
abbrev bodyTop (A : Semisentence LXI 1) : Semiformula LIinf ℕ 1 :=
  (Rew.emb ▹ formAt A Stage.top : Semiformula LIinf ℕ 1)

theorem unfold_top_eq (A : Semisentence LXI 1) (t : SyntacticTerm LIinf) :
    unfold A Stage.top t = (bodyTop A)/[t] := rfl

theorem emb_embK_eq_bodyTop (hX : XFreeL A) :
    (Rewriting.emb (embK A) : Semiformula LIinf ℕ 1) = bodyTop A := by
  rw [embK_eq_embed hX]; rfl

theorem emb_embK_closureAx (hX : XFreeL A) :
    (Rewriting.emb (embK (closureAx A)) : Proposition LIinf) =
      ∀¹ (∼(bodyTop A) ⋎ IOmegaAt (#0 : Semiterm LIinf ℕ 1)) := by
  rw [closureAx, embK_all, embK_imp, embK_Iat, Semiformula.imp_eq]
  simp only [Rewriting.app_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, rew_IOmegaAt, embT, Semiterm.lMap_bvar]
  rw [show ((Rew.emb).q ▹ embK A : Semiformula LIinf ℕ 1) = Rewriting.emb (embK A) by
    rw [Rew.q_emb], emb_embK_eq_bodyTop hX]
  rfl

theorem closure_inst (A : Semisentence LXI 1) (n : ℕ) :
    (∼(bodyTop A) ⋎ IOmegaAt (#0 : Semiterm LIinf ℕ 1))/[numI n] =
      ∼(unfold A Stage.top (numI n)) ⋎ IOmegaAt (numI n) := by
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    rew_IOmegaAt, Rew.subst_bvar, Matrix.cons_val_zero]
  rfl

theorem freeVariables_bodyTop (A : Semisentence LXI 1) : (bodyTop A).freeVariables = ∅ :=
  Semiformula.freeVariables_emb _

theorem params_bodyTop (A : Semisentence LXI 1) : params (bodyTop A) ⊆ {ThetaNote.Omega} := by
  rw [params_rew]; exact params_lMap_stageHom Stage.top A

/-- **Freund, Proposition 6.2**: the embedded closure axiom `∀x (A(x, I) → I x)` is derivable,
cut-free, at height `Ω + ω · m` for every nice operator. -/
theorem closure_derivable (hX : XFreeL A) :
    ∃ m : ℕ, ∀ H : Set ThetaNote → Set ThetaNote, ThetaNote.Nice H →
      IDerivable A ThetaNote.zero H
        (ThetaNote.nadd ThetaNote.Omega (ThetaNote.omegaMul (ThetaNote.ofNat m)))
        [(Rewriting.emb (embK (closureAx A)) : Proposition LIinf)] := by
  set c : ℕ := (bodyTop A).complexity with hc
  refine ⟨c + 1, fun H hH => ?_⟩
  have hΩ : ThetaNote.Omega ∈ H ∅ := hH.Omega_mem
  have hO : {ThetaNote.Omega} ⊆ H ∅ := Set.singleton_subset_iff.mpr hΩ
  set h2 : ThetaNote := ThetaNote.succ (ThetaNote.nadd ThetaNote.Omega
    (ThetaNote.omegaMul (ThetaNote.ofNat c))) with hh2
  have hmem : ∀ k, ThetaNote.nadd h2 (ThetaNote.ofNat k) ∈ H ∅ := fun k =>
    hH.nadd_mem (hH.succ_mem (hH.nadd_mem hΩ (hH.omegaMul_mem (hH.ofNat_mem c)))) (hH.ofNat_mem k)
  have h0 : ThetaNote.nadd h2 (ThetaNote.ofNat 0) = h2 := by
    rw [ThetaNote.ofNat_zero, ThetaNote.nadd_zero]
  have hlt : ∀ j k : ℕ, j < k → ThetaNote.nadd h2 (ThetaNote.ofNat j) <
      ThetaNote.nadd h2 (ThetaNote.ofNat k) := fun j k h => ThetaNote.nadd_ofNat_lt_nadd_ofNat _ h
  have hone : ∀ k, ThetaNote.one < ThetaNote.nadd h2 (ThetaNote.ofNat k) := fun k =>
    lt_of_lt_of_le (ThetaNote.one_lt_prin (p := ThetaNote.Omega) trivial)
      (le_trans (le_trans (ThetaNote.le_nadd_left _ _) (le_of_lt (ThetaNote.lt_succ _)))
        (ThetaNote.le_nadd_left _ _))
  set M : Proposition LIinf := ∀¹ (∼(bodyTop A) ⋎ IOmegaAt (#0 : Semiterm LIinf ℕ 1)) with hM
  have pM : params M ⊆ H ∅ := by
    rw [hM, params_all, params_or, params_neg]
    exact Set.union_subset ((params_bodyTop A).trans hO) (by simp [IOmegaAt]; exact hΩ)
  have pl : ∀ Δ : Sequent LIinf, (∀ χ ∈ Δ, params χ ⊆ {ThetaNote.Omega}) →
      paramsList Δ ⊆ H ∅ := by
    intro Δ h x ⟨χ, hχ, hx⟩; exact hO (h χ hχ hx)
  have hfin : ThetaNote.nadd h2 (ThetaNote.ofNat 2) <
      ThetaNote.nadd ThetaNote.Omega (ThetaNote.omegaMul (ThetaNote.ofNat (c + 1))) := by
    rw [hh2, ← ThetaNote.nadd_ofNat_one, ThetaNote.nadd_assoc, ThetaNote.nadd_assoc,
      ThetaNote.ofNat_nadd_ofNat]
    exact ThetaNote.nadd_lt_nadd_right _
      (ThetaNote.omegaMul_nadd_ofNat_lt (ThetaNote.ofNat_lt_ofNat (Nat.lt_succ_self c)) _)
  rw [emb_embK_closureAx hX]
  refine .all (fun _ => ThetaNote.nadd h2 (ThetaNote.ofNat 2))
    (hH.nadd_mem hΩ (hH.omegaMul_mem (hH.ofNat_mem _))) (by
      rw [paramsList_cons, paramsList_nil, Set.union_empty]; exact pM) List.mem_cons_self
    (fun _ => hfin) (fun n => ?_)
  rw [closure_inst]
  set U : Proposition LIinf := unfold A Stage.top (numI n) with hU
  set Q : Proposition LIinf := IOmegaAt (numI n) with hQ
  have pU : params U ⊆ {ThetaNote.Omega} := params_unfold A Stage.top (numI n)
  have pQ : params Q ⊆ {ThetaNote.Omega} := subset_refl _
  have pM' : params M ⊆ {ThetaNote.Omega} := by
    rw [hM, params_all, params_or, params_neg]
    exact Set.union_subset (params_bodyTop A) (subset_refl _)
  have pD : params (∼U ⋎ Q) ⊆ {ThetaNote.Omega} := by
    rw [params_or, params_neg]; exact Set.union_subset pU pQ
  have hcU : U.complexity = c := by rw [hU, unfold_top_eq, Semiformula.complexity_rew]
  -- Lemma 6.1 for `A(n̄, I^{≺Ω})`
  have t0 := taut (A := A) hH U (freeVariables_unfold Stage.top (numI_freeVariables n))
  rw [ThetaNote.adjoin_eq_self hH.isOperator (pU.trans hO)] at t0
  have hrk : ThetaNote.omegaMul (rk U) < h2 := by
    refine lt_of_le_of_lt ?_ (ThetaNote.lt_succ _)
    have := omegaMul_rk_le U
    rwa [hcU] at this
  have t1 : IDerivable A ThetaNote.zero H (ThetaNote.omegaMul (rk U))
      [U, ∼U, Q, ∼U ⋎ Q, M] :=
    t0.weaken_seq hH.isOperator (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
      (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl | rfl | rfl
        · exact pU
        · rw [params_neg]; exact pU
        · exact pQ
        · exact pD
        · exact pM'))
  -- clause (Fix)
  have t2 : IDerivable A ThetaNote.zero H h2 [∼U, Q, ∼U ⋎ Q, M] :=
    .fix (hH.succ_mem (hH.nadd_mem hΩ (hH.omegaMul_mem (hH.ofNat_mem c))))
      (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl | rfl
        · rw [params_neg]; exact pU
        · exact pQ
        · exact pD
        · exact pM'))
      (t := numI n) (List.mem_cons_of_mem _ List.mem_cons_self)
      (le_trans (ThetaNote.le_nadd_left _ _) (le_of_lt (ThetaNote.lt_succ _))) hrk t1
  have t3 : IDerivable A ThetaNote.zero H (ThetaNote.nadd h2 (ThetaNote.ofNat 1))
      [∼U, ∼U ⋎ Q, M] :=
    .orR (hmem 1) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl
        · rw [params_neg]; exact pU
        · exact pD
        · exact pM'))
      (List.mem_cons_of_mem _ List.mem_cons_self) (hone 1)
      (ThetaNote.lt_nadd_ofNat_succ h2 0)
      (t2.weaken_seq hH.isOperator (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
        (pl _ (by
          intro χ hχ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
          rcases hχ with rfl | rfl | rfl | rfl
          · exact pQ
          · rw [params_neg]; exact pU
          · exact pD
          · exact pM')))
  exact .orL (hmem 2) (pl _ (by
      intro χ hχ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
      rcases hχ with rfl | rfl
      · exact pD
      · exact pM'))
    List.mem_cons_self (hlt 1 2 (by omega)) t3

/-- **The closure axiom** in the form of the proof of Theorem 6.5. -/
theorem closure_axiom (hX : XFreeL A) : AxDerivable A (closureAx A) := by
  obtain ⟨m, hm⟩ := closure_derivable hX
  exact axDerivable_of_le 0 _ (nadd_Omega_le_OmegaTwo (omegaMul_ofNat_lt_Omega m) 0) hm

end Closure

/-! ### Ordinal sums for Proposition 6.4 -/

section Sums

open ThetaTerm in
/-- Finite ordinal and natural increments agree: `α + n = α ⊕ n`. -/
theorem ThetaNote.add_ofNat_eq_nadd (a : ThetaNote) :
    ∀ k : ℕ, a + ThetaNote.ofNat k = ThetaNote.nadd a (ThetaNote.ofNat k)
  | 0 => by rw [ThetaNote.ofNat_zero, ThetaNote.add_zero, ThetaNote.nadd_zero]
  | k + 1 => by
    have e1 : a + ThetaNote.ofNat (k + 1) = (a + ThetaNote.ofNat k) + ThetaNote.one := by
      rw [ThetaNote.add_assoc, ThetaNote.add_one_eq_succ, ← ThetaNote.ofNat_succ]
    rw [e1, ThetaNote.add_one_eq_succ, ThetaNote.add_ofNat_eq_nadd a k, ThetaNote.ofNat_succ]
    show ThetaNote.nadd (ThetaNote.nadd a (ThetaNote.ofNat k)) ThetaNote.one =
      ThetaNote.nadd a (ThetaNote.nadd (ThetaNote.ofNat k) ThetaNote.one)
    rw [ThetaNote.nadd_assoc]

theorem ThetaNote.le_add_right' (a b : ThetaNote) : a ≤ a + b := by
  have h := ThetaNote.add_le_add_left a (ThetaNote.zero_le' b)
  rwa [ThetaNote.add_zero] at h

open ThetaTerm in
/-- `(Ω ⊕ y) + Ω = Ω · 2` for `y ≺ Ω`: the summands of `y` are absorbed. -/
theorem ThetaNote.nadd_Omega_add_Omega {y : ThetaNote} (hy : y < ThetaNote.Omega) :
    ThetaNote.nadd ThetaNote.Omega y + ThetaNote.Omega =
      ThetaNote.nadd ThetaNote.Omega ThetaNote.Omega := by
  have hy' : ∀ e ∈ y.entries, e < ThetaTerm.Omega := (ThetaNote.lt_prin_iff (p := ThetaNote.Omega) trivial).mp hy
  have e1 : (ThetaNote.nadd ThetaNote.Omega y).entries = ThetaTerm.Omega :: y.entries := by
    rw [ThetaNote.entries_nadd, ThetaNote.entries_Omega]
    cases hys : y.entries with
    | nil => exact mergeL_nil_right _
    | cons y0 ys =>
      rw [mergeL_cons_cons_of_le [] ys
        (le_of_lt' (hy' y0 (by rw [hys]; exact List.mem_cons_self))), mergeL_nil_left]
  refine ThetaNote.ext_entries ?_
  rw [ThetaNote.entries_add, e1, ThetaNote.entries_Omega, addL_cons, ThetaNote.entries_nadd,
    ThetaNote.entries_Omega, mergeL_cons_cons_of_le [] [] (le_refl' _), mergeL_nil_left]
  rw [List.filter_cons_of_pos (by simp [geb]),
    List.filter_eq_nil_iff.mpr (fun e he => by
      simp only [geb, decide_eq_true_eq]
      exact not_le_of_lt' (hy' e he))]
  rfl

/-- `ω · (Ω ⊕ c) + ω · Ω = Ω · 2`. -/
theorem omegaMul_beta_add_Omega (c : ℕ) :
    ThetaNote.omegaMul (ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat c)) +
        ThetaNote.omegaMul ThetaNote.Omega = OmegaTwo := by
  rw [ThetaNote.omegaMul_nadd, ThetaNote.omegaMul_Omega]
  exact ThetaNote.nadd_Omega_add_Omega (omegaMul_ofNat_lt_Omega c)

/-- The step of the induction on stages: `(ω·β + ω·γ) ⊕ k ≺ ω·β + ω·δ` for `γ ≺ δ`. -/
theorem stage_sum_lt (b : ThetaNote) {g d : ThetaNote} (h : g < d) (k : ℕ) :
    ThetaNote.nadd (ThetaNote.omegaMul b + ThetaNote.omegaMul g) (ThetaNote.ofNat k) <
      ThetaNote.omegaMul b + ThetaNote.omegaMul d := by
  rw [← ThetaNote.add_ofNat_eq_nadd, ThetaNote.add_assoc, ThetaNote.add_ofNat_eq_nadd]
  exact ThetaNote.add_lt_add_left _ (ThetaNote.omegaMul_nadd_ofNat_lt h k)

end Sums

/-! ### Proposition 6.4: the induction axiom -/

section Induction

variable {A : Semisentence LXI 1} {H : Set ThetaNote → Set ThetaNote}

/-- `Cl(G) = ∀x (A(x, G) → G(x))`, the premise of the induction axiom. -/
def ClF (A : Semisentence LXI 1) (G : Semiformula LIinf ℕ 1) : Proposition LIinf :=
  ∀¹ (∼(plugI (predOf G) (bodyTop A)) ⋎ G)

theorem neg_ClF (A : Semisentence LXI 1) (G : Semiformula LIinf ℕ 1) :
    ∼(ClF A G) = ∃¹ (plugI (predOf G) (bodyTop A) ⋏ ∼G) := by
  simp [ClF]

theorem numSubst₁_eq_self {φ : Semiformula LIinf ℕ 1} (h : φ.freeVariables = ∅) (g : ℕ → ℕ) :
    numSubst₁ g ▹ φ = φ := by
  refine Semiformula.rew_eq_self_of (fun x => numSubst₁_bvar g x) ?_
  intro x hx
  have hx' : x ∈ φ.freeVariables := hx
  rw [h] at hx'
  exact absurd hx' (by simp)

/-- **The embedded induction axiom under a numeral assignment**: `¬Cl(G) ∨ ∀x (¬I x ∨ G(x))`
with `G = F⁺` under the assignment. -/
theorem indAx_inst (hX : XFreeL A) (F : Semiformula LXI ℕ 1) (g : ℕ → ℕ) :
    numSubst g ▹ embK ((∀¹ (opAt A F 🡒 F)) 🡒 ∀¹ (Iat #0 🡒 F)) =
      ∼(ClF A (numSubst₁ g ▹ embK F)) ⋎
        (∀¹ (∼(IOmegaAt (#0 : Semiterm LIinf ℕ 1)) ⋎ (numSubst₁ g ▹ embK F))) := by
  have hO : embK (opAt A F) = plugI (predOf (embK F)) (bodyTop A) := by
    rw [opAt, embK_substI, embK_emb, emb_embK_eq_bodyTop hX]
  simp only [Semiformula.imp_eq, embK_or, embK_neg, embK_all, embK_Iat, embT,
    Semiterm.lMap_bvar, hO, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    numSubst_all, rew_IOmegaAt]
  rw [rew_plugI_num, numSubst₁_eq_self (freeVariables_bodyTop A), numSubst₁_bvar]
  rfl

/-- **The induction on stages** in the proof of Proposition 6.4:
`H[δ] ⊢^{ω·β + ω·δ}_0 ¬Cl(G), ¬I^{≺δ} s, G(s)` for every stage `δ ⪯ Ω` and every closed `s`,
with `β = Ω ⊕ c`, `c` the complexity of `G`. -/
theorem indAx_claim (hA : Positive A) (hX : XFreeL A) (hH : ThetaNote.Nice H)
    (G : Semiformula LIinf ℕ 1) (hGf : G.freeVariables = ∅) (hGX : XFreeI G)
    (hGp : params G ⊆ {ThetaNote.Omega}) :
    ∀ (δ : Stage) (s : SyntacticTerm LIinf), s.freeVariables = ∅ →
      IDerivable A ThetaNote.zero (ThetaNote.adjoin H {δ.1})
        (ThetaNote.omegaMul (ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat G.complexity)) +
          ThetaNote.omegaMul δ.1)
        [∼(ClF A G), nstageAt δ s, G/[s]] := by
  set β : ThetaNote := ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat G.complexity) with hβ
  set Φ : Semiformula LIinf ℕ 1 := plugI (predOf G) (bodyTop A) with hΦ
  set cB : ℕ := (bodyTop A).complexity with hcB
  have hΩb : ThetaNote.Omega ≤ ThetaNote.omegaMul β := by
    rw [← ThetaNote.omegaMul_Omega]
    exact ThetaNote.omegaMul_le_omegaMul (ThetaNote.le_nadd_left _ _)
  have hαω : ∀ x : ThetaNote, omegaT ≤ ThetaNote.omegaMul β + ThetaNote.omegaMul x := fun x =>
    le_trans (le_of_lt (lt_of_lt_of_le (ThetaNote.omegaPow_lt_Omega
      (ThetaNote.one_lt_prin (p := ThetaNote.Omega) trivial)) hΩb)) (ThetaNote.le_add_right' _ _)
  have hrkG : ∀ x : ThetaNote,
      ThetaNote.omegaMul (rk G) ≤ ThetaNote.omegaMul β + ThetaNote.omegaMul x := fun x =>
    le_trans (ThetaNote.omegaMul_le_omegaMul (rk_le_Omega_nadd G)) (ThetaNote.le_add_right' _ _)
  have hΦf : Φ.freeVariables = ∅ :=
    freeVariables_plugI (predOf G) (freeVariables_predOf hGf) _ (freeVariables_bodyTop A)
  have hΦX : XFreeI Φ :=
    xFreeI_plugI (predOf G) (xFreeI_predOf hGX) _ (xFreeI_unfold_body hX Stage.top)
  have hΦp : params Φ ⊆ {ThetaNote.Omega} :=
    (params_plugI (predOf G) (params_predOf G) _).trans
      (Set.union_subset (params_bodyTop A) hGp)
  have hClp : params (∼(ClF A G)) ⊆ {ThetaNote.Omega} := by
    rw [params_neg, ClF, params_all, params_or, params_neg]
    exact Set.union_subset hΦp hGp
  suffices key : ∀ d : ThetaNote, ∀ δ : Stage, δ.1 = d → ∀ s : SyntacticTerm LIinf,
      s.freeVariables = ∅ →
      IDerivable A ThetaNote.zero (ThetaNote.adjoin H {δ.1})
        (ThetaNote.omegaMul β + ThetaNote.omegaMul δ.1) [∼(ClF A G), nstageAt δ s, G/[s]] from
    fun δ => key δ.1 δ rfl
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
  intro δ hδ s hs
  subst hδ
  have hKδ := hH.adjoin {δ.1}
  have hδmem : δ.1 ∈ ThetaNote.adjoin H {δ.1} ∅ := subset_adjoin_empty hH.isOperator _ rfl
  have hΩδ : ThetaNote.Omega ∈ ThetaNote.adjoin H {δ.1} ∅ := hKδ.Omega_mem
  have hαmem : ThetaNote.omegaMul β + ThetaNote.omegaMul δ.1 ∈ ThetaNote.adjoin H {δ.1} ∅ :=
    hKδ.add_mem (hKδ.omegaMul_mem (hKδ.nadd_mem hΩδ (hKδ.ofNat_mem _)))
      (hKδ.omegaMul_mem hδmem)
  have hPδ : paramsList [∼(ClF A G), nstageAt δ s, G/[s]] ⊆ ThetaNote.adjoin H {δ.1} ∅ := by
    intro x ⟨χ, hχ, hx⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
    rcases hχ with rfl | rfl | rfl
    · rw [Set.mem_singleton_iff.mp (hClp hx)]; exact hΩδ
    · rw [Set.mem_singleton_iff.mp hx]; exact hδmem
    · rw [params_subst] at hx; rw [Set.mem_singleton_iff.mp (hGp hx)]; exact hΩδ
  refine .nstage (fun g => ThetaNote.nadd (ThetaNote.omegaMul β + ThetaNote.omegaMul g.1)
    (ThetaNote.ofNat (2 * cB + 2))) hαmem hPδ (List.mem_cons_of_mem _ List.mem_cons_self)
    (fun g hg => stage_sum_lt β hg _) (fun g hg => ?_)
  -- the premise for `γ ≺ δ`
  set K := ThetaNote.adjoin (ThetaNote.adjoin H {δ.1}) {g.1} with hK
  have hKn : ThetaNote.Nice K := hKδ.adjoin {g.1}
  have hgK : g.1 ∈ K ∅ := subset_adjoin_empty hKδ.isOperator _ rfl
  have hΩK : ThetaNote.Omega ∈ K ∅ := hKn.Omega_mem
  have hO : {ThetaNote.Omega} ⊆ K ∅ := Set.singleton_subset_iff.mpr hΩK
  have hsubK : ThetaNote.adjoin H {δ.1} ∅ ⊆ K ∅ := hKδ.isOperator.mono (Set.empty_subset _)
  have hαg : ∀ k, ThetaNote.nadd (ThetaNote.omegaMul β + ThetaNote.omegaMul g.1)
      (ThetaNote.ofNat k) ∈ K ∅ := fun k =>
    hKn.nadd_mem (hKn.add_mem (hKn.omegaMul_mem (hKn.nadd_mem hΩK (hKn.ofNat_mem _)))
      (hKn.omegaMul_mem hgK)) (hKn.ofNat_mem k)
  have hαg0 : ThetaNote.omegaMul β + ThetaNote.omegaMul g.1 ∈ K ∅ := by
    have := hαg 0; rwa [ThetaNote.ofNat_zero, ThetaNote.nadd_zero] at this
  have hop : ∀ X, ThetaNote.adjoin H {g.1} X ⊆ K X := by
    intro X
    rw [hK, ThetaNote.adjoin_adjoin]
    exact adjoin_le_adjoin hH.isOperator Set.subset_union_right X
  have pl : ∀ Δ : Sequent LIinf, (∀ χ ∈ Δ, params χ ⊆ K ∅) → paramsList Δ ⊆ K ∅ := by
    intro Δ h x ⟨χ, hχ, hx⟩; exact h χ hχ hx
  have pCl : params (∼(ClF A G)) ⊆ K ∅ := hClp.trans hO
  have pGu : ∀ u : SyntacticTerm LIinf, params (G/[u]) ⊆ K ∅ := fun u => by
    rw [params_subst]; exact hGp.trans hO
  -- the hypothesis of Exercise 6.3, from the induction hypothesis at `γ`
  have hyp : ∀ u : SyntacticTerm LIinf, u.freeVariables = ∅ →
      IDerivable A ThetaNote.zero K (ThetaNote.omegaMul β + ThetaNote.omegaMul g.1)
        (∼(stageAt g u) :: G/[u] :: [∼(ClF A G)]) := by
    intro u hu
    refine (ih g.1 hg g rfl u hu).lift hKn.isOperator hop (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) (pl _ ?_)
    intro χ hχ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
    rcases hχ with rfl | rfl | rfl
    · rw [params_neg, params_stageAt]; exact Set.singleton_subset_iff.mpr hgK
    · exact pGu u
    · exact pCl
  have hUp : params (unfold A Stage.top s) ⊆ K ∅ := (params_unfold A Stage.top s).trans hO
  have E1 := ex63 hKn g G (hαω g.1) hαg0 [∼(ClF A G)] (pl _ (by
      intro χ hχ; rw [List.mem_singleton.mp hχ]; exact pCl)) hgK (hGp.trans hO) hyp cB
    (unfold A Stage.top s) (le_of_eq (by rw [unfold_top_eq, Semiformula.complexity_rew]))
    (opShape_unfold hA hX s) (freeVariables_unfold Stage.top hs) hUp
  rw [plugI_unfold, unfold_top_eq, ← rew_plugI_of G (fixF_subst _)] at E1
  -- Lemma 6.1 for `G(s)`
  have T := taut (A := A) hH (G/[s]) (freeVariables_subst_of_closed G hGf hs)
  rw [ThetaNote.adjoin_eq_self hH.isOperator (by
    rw [params_subst]; exact hGp.trans (Set.singleton_subset_iff.mpr hH.Omega_mem)),
    rk_subst] at T
  set C : Proposition LIinf := Φ/[s] ⋏ ∼(G/[s]) with hC
  have pC : params C ⊆ K ∅ := by
    rw [hC, params_and, params_neg, params_subst]; exact Set.union_subset (hΦp.trans hO) (pGu s)
  have pUg : params (∼(unfold A g s)) ⊆ K ∅ := by
    rw [params_neg]; exact (params_unfold A g s).trans (Set.singleton_subset_iff.mpr hgK)
  have pΔ : paramsList [C, ∼(unfold A g s), ∼(ClF A G), G/[s]] ⊆ K ∅ := pl _ (by
    intro χ hχ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
    rcases hχ with rfl | rfl | rfl | rfl
    · exact pC
    · exact pUg
    · exact pCl
    · exact pGu s)
  have E2 : IDerivable A ThetaNote.zero K
      (ThetaNote.nadd (ThetaNote.omegaMul β + ThetaNote.omegaMul g.1) (ThetaNote.ofNat (2 * cB + 1)))
      [C, ∼(unfold A g s), ∼(ClF A G), G/[s]] := by
    refine .and (hαg _) pΔ List.mem_cons_self
      (ThetaNote.nadd_ofNat_lt_nadd_ofNat _ (Nat.lt_succ_self _))
      (lt_of_le_of_lt (hrkG g.1) (ThetaNote.lt_nadd_ofNat_succ _ _)) ?_ ?_
    · refine E1.weaken_seq hKn.isOperator (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
      rw [paramsList_cons, params_subst]; exact Set.union_subset (hΦp.trans hO) pΔ
    · refine T.lift hKn.isOperator
        (fun X => hH.isOperator.mono (Set.subset_union_right.trans Set.subset_union_right))
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
      rw [paramsList_cons, params_neg]; exact Set.union_subset (pGu s) pΔ
  -- the numeral of the value of `s`
  have hCs : C = (Φ ⋏ ∼G)/[s] := by
    rw [hC]; simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg]
  have hsim : Sim C ((Φ ⋏ ∼G)/[numI (closedVal s)]) := by
    rw [hCs]
    exact sim_subst_numI (φ := Φ ⋏ ∼G) (by
      rw [Semiformula.freeVariables_and, Semiformula.freeVariables_not, hΦf, hGf]; rfl)
      (show XFreeI Φ ∧ XFreeI (∼G) from ⟨hΦX, (xFreeI_neg G).mpr hGX⟩) hs
  have E3 := E2.replace_head hX hKn.isOperator hsim
  have E4 : IDerivable A ThetaNote.zero K
      (ThetaNote.nadd (ThetaNote.omegaMul β + ThetaNote.omegaMul g.1) (ThetaNote.ofNat (2 * cB + 2)))
      [∼(unfold A g s), ∼(ClF A G), G/[s]] :=
    .exs (closedVal s) (hαg _) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl
        · exact pUg
        · exact pCl
        · exact pGu s))
      (by rw [← neg_ClF]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      (lt_of_lt_of_le (ThetaNote.ofNat_lt_omega _)
        (le_trans (hαω g.1) (ThetaNote.le_nadd_left _ _)))
      (ThetaNote.nadd_ofNat_lt_nadd_ofNat _ (Nat.lt_succ_self _)) E3
  refine E4.weaken_seq hKn.isOperator (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
  refine pl _ ?_
  intro χ hχ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
  rcases hχ with rfl | rfl | rfl | rfl
  · exact pUg
  · exact pCl
  · rw [params_nstageAt]; exact Set.singleton_subset_iff.mpr (hsubK hδmem)
  · exact pGu s

end Induction

/-! ### Proposition 6.4, the axiom -/

section IndAxiom

variable {A : Semisentence LXI 1} {H : Set ThetaNote → Set ThetaNote}

theorem indBody_inst (G : Semiformula LIinf ℕ 1) (n : ℕ) :
    (∼(IOmegaAt (#0 : Semiterm LIinf ℕ 1)) ⋎ G)/[numI n] = ∼(IOmegaAt (numI n)) ⋎ G/[numI n] := by
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    rew_IOmegaAt, Rew.subst_bvar, Matrix.cons_val_zero]

/-- **Freund, Proposition 6.4**, for the instance with the free variables replaced by
numerals: `H ⊢^{Ω·2 + 5}_0 Cl(G) → ∀x (I x → G(x))`. -/
theorem indAx_closed_derivable (hA : Positive A) (hX : XFreeL A) (hH : ThetaNote.Nice H)
    (G : Semiformula LIinf ℕ 1) (hGf : G.freeVariables = ∅) (hGX : XFreeI G)
    (hGp : params G ⊆ {ThetaNote.Omega}) :
    IDerivable A ThetaNote.zero H (ThetaNote.nadd OmegaTwo (ThetaNote.ofNat 5))
      [∼(ClF A G) ⋎ (∀¹ (∼(IOmegaAt (#0 : Semiterm LIinf ℕ 1)) ⋎ G))] := by
  have hΩ : ThetaNote.Omega ∈ H ∅ := hH.Omega_mem
  have hO : {ThetaNote.Omega} ⊆ H ∅ := Set.singleton_subset_iff.mpr hΩ
  have hmem : ∀ k, ThetaNote.nadd OmegaTwo (ThetaNote.ofNat k) ∈ H ∅ := OmegaTwo_mem hH ∅
  have hlt : ∀ j k : ℕ, j < k → ThetaNote.nadd OmegaTwo (ThetaNote.ofNat j) <
      ThetaNote.nadd OmegaTwo (ThetaNote.ofNat k) := fun j k h =>
    ThetaNote.nadd_ofNat_lt_nadd_ofNat _ h
  have hone : ∀ k, ThetaNote.one < ThetaNote.nadd OmegaTwo (ThetaNote.ofNat k) := fun k =>
    lt_of_lt_of_le (ThetaNote.one_lt_prin (p := ThetaNote.Omega) trivial)
      (Omega_le_OmegaTwo_nadd k)
  have hO2 : OmegaTwo < ThetaNote.nadd OmegaTwo (ThetaNote.ofNat 1) :=
    ThetaNote.lt_nadd_ofNat_succ _ 0
  set Cl : Proposition LIinf := ∼(ClF A G) with hCl
  set V : Proposition LIinf := ∀¹ (∼(IOmegaAt (#0 : Semiterm LIinf ℕ 1)) ⋎ G) with hV
  have pΦ : params (plugI (predOf G) (bodyTop A)) ⊆ {ThetaNote.Omega} :=
    (params_plugI (predOf G) (params_predOf G) _).trans (Set.union_subset (params_bodyTop A) hGp)
  have pCl : params Cl ⊆ {ThetaNote.Omega} := by
    rw [hCl, params_neg, ClF, params_all, params_or, params_neg]; exact Set.union_subset pΦ hGp
  have pV : params V ⊆ {ThetaNote.Omega} := by
    rw [hV, params_all, params_or, params_neg]; exact Set.union_subset (subset_refl _) hGp
  have pM : params (Cl ⋎ V) ⊆ {ThetaNote.Omega} := by
    rw [params_or]; exact Set.union_subset pCl pV
  have pGn : ∀ n, params (G/[numI n]) ⊆ {ThetaNote.Omega} := fun n => by rw [params_subst]; exact hGp
  have pIn : ∀ n, params (∼(IOmegaAt (numI n))) ⊆ {ThetaNote.Omega} := fun n => by
    rw [params_neg]; exact subset_refl _
  have pDn : ∀ n, params (∼(IOmegaAt (numI n)) ⋎ G/[numI n]) ⊆ {ThetaNote.Omega} := fun n => by
    rw [params_or]; exact Set.union_subset (pIn n) (pGn n)
  have pl : ∀ Δ : Sequent LIinf, (∀ χ ∈ Δ, params χ ⊆ {ThetaNote.Omega}) →
      paramsList Δ ⊆ H ∅ := by
    intro Δ h x ⟨χ, hχ, hx⟩; exact hO (h χ hχ hx)
  -- the ω-rule on `∀x (¬I x ∨ G(x))`
  have p4 : IDerivable A ThetaNote.zero H (ThetaNote.nadd OmegaTwo (ThetaNote.ofNat 3)) [Cl, V] := by
    refine .all (fun _ => ThetaNote.nadd OmegaTwo (ThetaNote.ofNat 2)) (hmem 3) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl
        · exact pCl
        · exact pV)) (List.mem_cons_of_mem _ List.mem_cons_self)
      (fun _ => hlt 2 3 (by omega)) (fun n => ?_)
    rw [indBody_inst]
    set D : Proposition LIinf := ∼(IOmegaAt (numI n)) ⋎ G/[numI n] with hD
    -- the induction on stages, at `δ = Ω`
    have c0 := indAx_claim hA hX hH G hGf hGX hGp Stage.top (numI n) (numI_freeVariables n)
    rw [Stage.top_val, ThetaNote.adjoin_eq_self hH.isOperator (Set.singleton_subset_iff.mpr hΩ),
      omegaMul_beta_add_Omega] at c0
    have p1 : IDerivable A ThetaNote.zero H OmegaTwo
        [G/[numI n], ∼(IOmegaAt (numI n)), D, Cl, V] :=
      c0.weaken_seq hH.isOperator (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl) (pl _ (by
          intro χ hχ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
          rcases hχ with rfl | rfl | rfl | rfl | rfl
          · exact pGn n
          · exact pIn n
          · exact pDn n
          · exact pCl
          · exact pV))
    have p2 : IDerivable A ThetaNote.zero H (ThetaNote.nadd OmegaTwo (ThetaNote.ofNat 1))
        [∼(IOmegaAt (numI n)), D, Cl, V] :=
      .orR (hmem 1) (pl _ (by
          intro χ hχ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
          rcases hχ with rfl | rfl | rfl | rfl
          · exact pIn n
          · exact pDn n
          · exact pCl
          · exact pV))
        (List.mem_cons_of_mem _ List.mem_cons_self) (hone 1) hO2 p1
    exact .orL (hmem 2) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl
        · exact pDn n
        · exact pCl
        · exact pV))
      List.mem_cons_self (hlt 1 2 (by omega)) p2
  -- the two disjunctions
  have p5 : IDerivable A ThetaNote.zero H (ThetaNote.nadd OmegaTwo (ThetaNote.ofNat 4))
      [Cl, Cl ⋎ V] :=
    .orR (hmem 4) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl
        · exact pCl
        · exact pM))
      (List.mem_cons_of_mem _ List.mem_cons_self) (hone 4) (hlt 3 4 (by omega))
      (p4.weaken_seq hH.isOperator (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
        (pl _ (by
          intro χ hχ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
          rcases hχ with rfl | rfl | rfl
          · exact pV
          · exact pCl
          · exact pM)))
  exact .orL (hmem 5) (pl _ (by
      intro χ hχ; rw [List.mem_singleton.mp hχ]; exact pM))
    List.mem_cons_self (hlt 4 5 (by omega)) p5

/-- **The induction axiom** `indAx A F` (Freund, Proposition 6.4, and the universal closure
in the proof of Theorem 6.5). -/
theorem indAx_axiom (hA : Positive A) (hX : XFreeL A) (F : Semiformula LXI ℕ 1) :
    AxDerivable A (indAx A F) := by
  set ψ0 : Proposition LXI := (∀¹ (opAt A F 🡒 F)) 🡒 ∀¹ (Iat #0 🡒 F) with hψ0
  refine axDerivable_of_le (5 + (0 + ψ0.fvSup))
    (ThetaNote.nadd (ThetaNote.nadd OmegaTwo (ThetaNote.ofNat 5))
      (ThetaNote.ofNat (0 + ψ0.fvSup)))
    (le_of_eq (by rw [ThetaNote.nadd_assoc, ThetaNote.ofNat_nadd_ofNat])) (fun H hH => ?_)
  have hΩ : ThetaNote.Omega ∈ H ∅ := hH.Omega_mem
  have hO : {ThetaNote.Omega} ⊆ H ∅ := Set.singleton_subset_iff.mpr hΩ
  rw [indAx, emb_embK_univCl]
  refine allClosure_derivable hH.isOperator _
    (fun j => hH.nadd_mem (OmegaTwo_mem hH ∅ 5) (hH.ofNat_mem j))
    ((params_embK _).trans hO) (fun w => ?_)
  rw [embK_fixitr_inst, indAx_inst hX]
  set g : ℕ → ℕ := fun y => if hy : y < 0 + ψ0.fvSup then w ⟨y, hy⟩ else 0 with hg
  exact indAx_closed_derivable hA hX hH (numSubst₁ g ▹ embK F) (freeVariables_numSubst₁ g _)
    ((xFreeI_rew (numSubst₁ g) _).mpr (xFreeI_embK F)) (by rw [params_rew]; exact params_embK F)

end IndAxiom

end InductiveDef

end OrdinalAnalysis
