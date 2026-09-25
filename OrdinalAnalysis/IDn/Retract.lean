/-
  The retraction `LXIω →ᵥ LXIn m` (`m ≥ 1`), and `IDseqToIDn`: every `IDseq (WFormsOmega F) m`
  derivation of `TI_{Omega 0}` (in `LXIω` directly) retracts to an honest `IDn m (WForms F m)`
  derivation (in the smaller language `LXIn m`) of the same sentence, closing the one further
  open link `Theorem2.lean`'s `idlt_theorem` needs (`IDseqToIDn`, `Theorem2.lean`'s own docstring:
  "not built" in `Union.lean`).

  **The retraction.** `retrFun m hm : ℕ → Fin m` is the identity on `{0, …, m-1}` and sends every
  `j ≥ m` to `⟨m-1, _⟩`; `retr m hm := mapHom (retrFun m hm) : LXIω →ᵥ LXIn m` fixes arithmetic
  and `X`, sends `I_j ↦ I_j` for `j < m`. `embedOmega m ∘ retr m hm` is not literally the
  identity, but `retr m hm` is a genuine *retraction* of `embedOmega m` in the sense that matters
  here: it fixes every symbol `embedOmega m` introduces (`lMap_embedOmega_retr`).

  **The route.** A derivation `IDseq (WFormsOmega F) m ⊢ σ` maps, along `retr m hm`, to a
  derivation `Theory.lMap (retr m hm) (IDseq (WFormsOmega F) m) ⊢ Semiformula.lMap (retr m hm) σ`
  (`theory_proof_lMap`, built from `Derivation.lMap` and `Theory.Proof.provable_iff` — the
  translation-of-derivations lemma `Union.lean`'s docstring says is not built). Since
  `tiUptoSentence` never mentions any `I_j` (only `X` and arithmetic), it is fixed by *any*
  `mapHom` (`lMap_tiUptoSentence`). And every axiom of `IDseq (WFormsOmega F) m` translates,
  along `retr m hm`, to a literal axiom of `IDn m (WForms F m)` (`idseq_lMap_subset`): the `PA`
  part translates along `toLXIN`/the induction scheme/`𝗘𝗤` generically (`paLXIN_lMap_subset`),
  and the closure/induction axioms of each level `k < m` translate via `lMap_closureAxAt`
  (`Union.lean`, already built) and the new `lMap_indAxAt` (built here from `lMap_substIAt`,
  needing only that the operator form `WFormsOmega F k` is level-bounded at `k` — `k < m` keeps
  `retrFun` injective on the levels `WFormsOmega F k` actually mentions, so no level `≥ m`
  collision ever touches an atom that matters).

  **The one gap `IDseqToIDn`'s own statement leaves.** For `m = 0`, `IDseq (WFormsOmega F) 0 =
  paLXIN ℕ` has no `I`-axioms at all, and `retrFun 0 _` cannot exist (`Fin 0` is empty) — the
  retraction route does not apply, and `IDseqToIDn`'s existential asks for `0 < 0`, impossible.
  `idseq_to_idn` closes this the only way available: weaken the hypothesised `m = 0` proof up to
  `IDseq (WFormsOmega F) 1` (`IDseq_mono`, cumulative), retract that to an honest `IDn 1
  (WForms F 1)` proof, and refute it with `idn_lower_bound` at `n := 1` — hence the two extra
  hypotheses `hyps1`/`hcol1`, exactly `idlt_theorem`'s own `hyps`/`hcol` specialised to level `1`.

  Contents.

    `retrFun`, `retr`                                 the retraction `LXIω →ᵥ LXIn m`, `m ≥ 1`
    `lm_mapHom`                                        arithmetic is fixed by any `mapHom`
    `wForm_congr`, `lMap_wForm`                        `wForm`'s translation along any `mapHom`
    `lMap_tiUptoSentence`                              `TI_a` is fixed by any `mapHom`
    `lMap_univCl`, `lMap_succInd`                      the two schema-building blocks
    `eqAxiom_lMap_subset`, `paLXIN_lMap_subset`         the `PA` part translates
    `lMap_substIAt_of_levelBounded`, `lMap_indAxAt`     the induction axiom translates
    `theory_proof_lMap`                                **the translation-of-derivations lemma**
    `idseq_lMap_subset`, `retraction_step`              the retraction, assembled
    `idseq_to_idn`                                      **`IDseqToIDn orderFormulas (Omega 0)`**
-/
import OrdinalAnalysis.IDn.Theorem2
import OrdinalAnalysis.IDn.UpperFormsFacts

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.IDn.Upper

/-! ### The retraction `LXIω →ᵥ LXIn m` -/

/-- The identity on `{0, …, m-1}`, constant `⟨m-1, _⟩` above. -/
def retrFun (m : ℕ) (hm : 0 < m) (j : ℕ) : Fin m :=
  if h : j < m then ⟨j, h⟩ else ⟨m - 1, by omega⟩

theorem retrFun_eq_of_lt {m : ℕ} (hm : 0 < m) {j : ℕ} (hj : j < m) :
    retrFun m hm j = ⟨j, hj⟩ := dif_pos hj

theorem retrFun_ne_of_lt {m : ℕ} (hm : 0 < m) {i j : ℕ} (hi : i < m) (hj : j < m) (hij : i ≠ j) :
    retrFun m hm i ≠ retrFun m hm j := by
  rw [retrFun_eq_of_lt hm hi, retrFun_eq_of_lt hm hj]
  intro h
  exact hij (congrArg Fin.val h)

/-- **The retraction of `LXIω` into `LXIn m`, for `m ≥ 1`.** Fixes arithmetic and `X`, sends
`I_j ↦ I_j` for `j < m`. -/
def retr (m : ℕ) (hm : 0 < m) : LXIomega →ᵥ LXIn m := mapHom (retrFun m hm)

/-! ### Arithmetic is fixed by any `mapHom` -/

theorem term_lm_mapHom {ι ι' : Type} (g : ι → ι') {ξ : Type*} {n : ℕ} :
    ∀ (t : Semiterm ℒₒᵣ ξ n),
      Semiterm.lMap (mapHom g) (Semiterm.lMap (toLXIN ι) t) = Semiterm.lMap (toLXIN ι') t
  | .bvar x => rfl
  | .fvar x => rfl
  | .func h w => by
      have e1 : Semiterm.lMap (mapHom g) (Semiterm.lMap (toLXIN ι) (Semiterm.func h w)) =
          Semiterm.func ((mapHom g).func ((toLXIN ι).func h))
            (fun i => Semiterm.lMap (mapHom g) (Semiterm.lMap (toLXIN ι) (w i))) := rfl
      have e2 : Semiterm.lMap (toLXIN ι') (Semiterm.func h w) =
          Semiterm.func ((toLXIN ι').func h) (fun i => Semiterm.lMap (toLXIN ι') (w i)) := rfl
      rw [e1, e2]
      congr 1
      funext i
      exact term_lm_mapHom g (w i)

theorem lm_mapHom {ι ι' : Type} (g : ι → ι') :
    ∀ {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n),
      Semiformula.lMap (mapHom g) (lm (ι := ι) φ) = lm (ι := ι') φ := by
  intro ξ n φ
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
      have e1 : Semiformula.lMap (mapHom g) (lm (ι := ι) (Semiformula.rel r v)) =
          Semiformula.rel ((mapHom g).rel ((toLXIN ι).rel r))
            (fun i => Semiterm.lMap (mapHom g) (Semiterm.lMap (toLXIN ι) (v i))) := rfl
      have e2 : lm (ι := ι') (Semiformula.rel r v) =
          Semiformula.rel ((toLXIN ι').rel r) (fun i => Semiterm.lMap (toLXIN ι') (v i)) := rfl
      rw [e1, e2]
      congr 1
      funext i
      exact term_lm_mapHom g (v i)
  | hnrel r v =>
      have e1 : Semiformula.lMap (mapHom g) (lm (ι := ι) (Semiformula.nrel r v)) =
          Semiformula.nrel ((mapHom g).rel ((toLXIN ι).rel r))
            (fun i => Semiterm.lMap (mapHom g) (Semiterm.lMap (toLXIN ι) (v i))) := rfl
      have e2 : lm (ι := ι') (Semiformula.nrel r v) =
          Semiformula.nrel ((toLXIN ι').rel r) (fun i => Semiterm.lMap (toLXIN ι') (v i)) := rfl
      rw [e1, e2]
      congr 1
      funext i
      exact term_lm_mapHom g (v i)
  | hand φ ψ ihφ ihψ =>
      show Semiformula.lMap (mapHom g) (lm (ι := ι) φ ⋏ lm (ι := ι) ψ) = _
      rw [LogicalConnective.HomClass.map_and, ihφ, ihψ]; rfl
  | hor φ ψ ihφ ihψ =>
      show Semiformula.lMap (mapHom g) (lm (ι := ι) φ ⋎ lm (ι := ι) ψ) = _
      rw [LogicalConnective.HomClass.map_or, ihφ, ihψ]; rfl
  | hall φ ih =>
      show Semiformula.lMap (mapHom g) (∀¹ lm (ι := ι) φ) = _
      rw [Semiformula.lMap_all, ih]; rfl
  | hexs φ ih =>
      show Semiformula.lMap (mapHom g) (∃¹ lm (ι := ι) φ) = _
      rw [Semiformula.lMap_exs, ih]; rfl

/-! ### `wForm`'s translation along any `mapHom` -/

theorem DF_congr (F : OrderFormulas) {ι : Type} {ix ix' : ℕ → ι} :
    ∀ (n : ℕ), (∀ i < n, ix i = ix' i) → DF F ix n = DF F ix' n
  | 0, _ => rfl
  | n + 1, h => by
      show DF F ix n ⋏ (∀¹ (lm (inEAt n) 🡒 Iat (ix n) #0)) =
        DF F ix' n ⋏ (∀¹ (lm (inEAt n) 🡒 Iat (ix' n) #0))
      rw [DF_congr F n (fun i hi => h i (by omega)), h n (by omega)]

theorem wForm_congr (F : OrderFormulas) {ι : Type} {ix ix' : ℕ → ι} :
    ∀ (n : ℕ), (∀ i ≤ n, ix i = ix' i) → wForm F ix n = wForm F ix' n
  | 0, h => by
      show (∀¹ (lm (OrderFormulas.precW F) 🡒 Iat (ix 0) #0)) =
        ∀¹ (lm (OrderFormulas.precW F) 🡒 Iat (ix' 0) #0)
      rw [h 0 (le_refl 0)]
  | n + 1, h => by
      show DF F ix (n + 1) ⋏ (lm (ltOmegaAt F (n + 1)) ⋏
          (∀¹ ((DF F ix (n + 1) ⇜ ![#0]) ⋏ lm F.ltDef.val 🡒 Iat (ix (n + 1)) #0))) =
        DF F ix' (n + 1) ⋏ (lm (ltOmegaAt F (n + 1)) ⋏
          (∀¹ ((DF F ix' (n + 1) ⇜ ![#0]) ⋏ lm F.ltDef.val 🡒 Iat (ix' (n + 1)) #0)))
      rw [DF_congr F (n + 1) (fun i hi => h i (by omega)), h (n + 1) (le_refl _)]

theorem lMap_DF {ι ι' : Type} (g : ι → ι') (F : OrderFormulas) (ix : ℕ → ι) :
    ∀ (n : ℕ), Semiformula.lMap (mapHom g) (DF F ix n) = DF F (g ∘ ix) n
  | 0 => lm_mapHom g F.fldWDef.val
  | n + 1 => by
      show Semiformula.lMap (mapHom g) (DF F ix n ⋏ (∀¹ (lm (inEAt n) 🡒 Iat (ix n) #0))) =
        DF F (g ∘ ix) n ⋏ (∀¹ (lm (inEAt n) 🡒 Iat (g (ix n)) #0))
      rw [LogicalConnective.HomClass.map_and, lMap_DF g F ix n, Semiformula.lMap_all,
        LogicalConnective.HomClass.map_imply, lm_mapHom g (inEAt n), lMap_Iat,
        Semiterm.lMap_bvar]

theorem lMap_wForm {ι ι' : Type} (g : ι → ι') (F : OrderFormulas) (ix : ℕ → ι) :
    ∀ (n : ℕ), Semiformula.lMap (mapHom g) (wForm F ix n) = wForm F (g ∘ ix) n
  | 0 => by
      show Semiformula.lMap (mapHom g) (∀¹ (lm (OrderFormulas.precW F) 🡒 Iat (ix 0) #0)) =
        ∀¹ (lm (OrderFormulas.precW F) 🡒 Iat (g (ix 0)) #0)
      rw [Semiformula.lMap_all, LogicalConnective.HomClass.map_imply,
        lm_mapHom g (OrderFormulas.precW F), lMap_Iat, Semiterm.lMap_bvar]
  | n + 1 => by
      show Semiformula.lMap (mapHom g) (DF F ix (n + 1) ⋏ (lm (ltOmegaAt F (n + 1)) ⋏
          (∀¹ ((DF F ix (n + 1) ⇜ ![#0]) ⋏ lm F.ltDef.val 🡒 Iat (ix (n + 1)) #0)))) =
        DF F (g ∘ ix) (n + 1) ⋏ (lm (ltOmegaAt F (n + 1)) ⋏
          (∀¹ ((DF F (g ∘ ix) (n + 1) ⇜ ![#0]) ⋏ lm F.ltDef.val 🡒 Iat (g (ix (n + 1))) #0)))
      rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and,
        lMap_DF g F ix (n + 1), lm_mapHom g (ltOmegaAt F (n + 1)), Semiformula.lMap_all,
        LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
        Semiformula.lMap_subst, lm_mapHom g F.ltDef.val,
        lMap_Iat, Semiterm.lMap_bvar, lMap_DF g F ix (n + 1)]
      simp [Matrix.comp₁]

/-! ### `TI_a` is fixed by any `mapHom` -/

theorem lMap_tiUptoSentence {ι ι' : Type} (g : ι → ι') (F : OrderFormulas) (a : ThetaWNoteD) :
    Semiformula.lMap (mapHom g) (Upper.tiUptoSentence F ι a) = Upper.tiUptoSentence F ι' a := by
  show Semiformula.lMap (mapHom g)
      ((∀¹ ((∀¹ (lm (OrderFormulas.precW F) 🡒 Xat #0)) 🡒 Xat #0)) 🡒
        ∀¹ (lm (Upper.belowC F a) 🡒 Xat #0)) =
    (∀¹ ((∀¹ (lm (OrderFormulas.precW F) 🡒 Xat #0)) 🡒 Xat #0)) 🡒
      ∀¹ (lm (Upper.belowC F a) 🡒 Xat #0)
  rw [LogicalConnective.HomClass.map_imply, Semiformula.lMap_all,
    LogicalConnective.HomClass.map_imply, Semiformula.lMap_all,
    LogicalConnective.HomClass.map_imply, lm_mapHom g (OrderFormulas.precW F),
    lMap_Xat, Semiterm.lMap_bvar, lMap_Xat, Semiformula.lMap_all,
    LogicalConnective.HomClass.map_imply, lm_mapHom g (Upper.belowC F a), lMap_Xat,
    Semiterm.lMap_bvar]

/-! ### The two schema-building blocks -/

theorem lMap_fixitr {L₁ L₂ : Language} (Φ : L₁ →ᵥ L₂) (n : ℕ) :
    ∀ (m : ℕ) (φ : Semiformula L₁ ℕ n),
      Semiformula.lMap Φ (Rew.fixitr n m ▹ φ) = Rew.fixitr n m ▹ Semiformula.lMap Φ φ
  | 0, φ => by simp
  | m + 1, φ => by
      simp only [Rew.fixitr_succ, TransitiveRewriting.comp_app]
      rw [Semiformula.lMap_fix, lMap_fixitr Φ n m φ]

theorem lMap_univCl' {L₁ L₂ : Language} (Φ : L₁ →ᵥ L₂) (φ : Proposition L₁) :
    Semiformula.lMap Φ φ.univCl' = (Semiformula.lMap Φ φ).univCl' := by
  have hfvSup : (Semiformula.lMap Φ φ).fvSup = φ.fvSup := by
    unfold Semiformula.fvSup
    rw [Semiformula.freeVariables_lMap]
  show Semiformula.lMap Φ (∀¹* (Rew.fixitr 0 φ.fvSup ▹ φ)) =
    ∀¹* (Rew.fixitr 0 (Semiformula.lMap Φ φ).fvSup ▹ Semiformula.lMap Φ φ)
  rw [Semiformula.lMap_allClosure, lMap_fixitr, hfvSup]

theorem lMap_univCl {L₁ L₂ : Language} (Φ : L₁ →ᵥ L₂) (φ : Proposition L₁) :
    Semiformula.lMap Φ (Semiformula.univCl φ) = Semiformula.univCl (Semiformula.lMap Φ φ) := by
  refine (Semiformula.coe_inj _ _).mp ?_
  rw [← Semiformula.lMap_emb (Φ := Φ) (Semiformula.univCl φ), Semiformula.coe_univCl_eq_univCl',
    Semiformula.coe_univCl_eq_univCl', lMap_univCl']

theorem lMap_mapHom_zero {ι ι' : Type} (g : ι → ι') {ξ : Type*} {n : ℕ} :
    Semiterm.lMap (mapHom g) (((0 : ℕ) : Semiterm (LXIN ι) ξ n)) =
      ((0 : ℕ) : Semiterm (LXIN ι') ξ n) := by
  show Semiterm.lMap (mapHom g) (Semiterm.Operator.numeral (LXIN ι) 0) =
    Semiterm.Operator.numeral (LXIN ι') 0
  rw [Semiterm.Operator.numeral_zero, Semiterm.Operator.numeral_zero]
  show Semiterm.lMap (mapHom g) (Semiterm.Operator.Zero.zero.operator ![]) =
    (Semiterm.Operator.Zero.zero : Semiterm.Operator (LXIN ι') 0).operator ![]
  show Semiterm.lMap (mapHom g)
      (Rew.subst ![] (Rew.emb (Semiterm.func Language.Zero.zero ![]))) =
    Rew.subst ![] (Rew.emb (Semiterm.func Language.Zero.zero ![]))
  simp
  rfl

theorem lMap_mapHom_one {ι ι' : Type} (g : ι → ι') {ξ : Type*} {n : ℕ} :
    Semiterm.lMap (mapHom g) (((1 : ℕ) : Semiterm (LXIN ι) ξ n)) =
      ((1 : ℕ) : Semiterm (LXIN ι') ξ n) := by
  show Semiterm.lMap (mapHom g) (Semiterm.Operator.numeral (LXIN ι) 1) =
    Semiterm.Operator.numeral (LXIN ι') 1
  rw [Semiterm.Operator.numeral_one, Semiterm.Operator.numeral_one]
  show Semiterm.lMap (mapHom g) (Semiterm.Operator.One.one.operator ![]) =
    (Semiterm.Operator.One.one : Semiterm.Operator (LXIN ι') 0).operator ![]
  show Semiterm.lMap (mapHom g)
      (Rew.subst ![] (Rew.emb (Semiterm.func Language.One.one ![]))) =
    Rew.subst ![] (Rew.emb (Semiterm.func Language.One.one ![]))
  simp
  rfl

theorem lMap_mapHom_addOp {ι ι' : Type} (g : ι → ι') {ξ : Type*} {n : ℕ}
    (t u : Semiterm (LXIN ι) ξ n) :
    Semiterm.lMap (mapHom g) (Semiterm.Operator.Add.add.operator ![t, u]) =
      Semiterm.Operator.Add.add.operator ![Semiterm.lMap (mapHom g) t, Semiterm.lMap (mapHom g) u] := by
  show Semiterm.lMap (mapHom g)
      (Rew.subst ![t, u] (Rew.emb (Semiterm.func Language.Add.add Semiterm.bvar))) =
    Rew.subst ![Semiterm.lMap (mapHom g) t, Semiterm.lMap (mapHom g) u]
      (Rew.emb (Semiterm.func Language.Add.add Semiterm.bvar))
  rw [show Rew.subst ![t, u] (Rew.emb (Semiterm.func Language.Add.add Semiterm.bvar)) =
        Semiterm.func Language.Add.add ![t, u] from rfl,
    show Rew.subst ![Semiterm.lMap (mapHom g) t, Semiterm.lMap (mapHom g) u]
        (Rew.emb (Semiterm.func Language.Add.add Semiterm.bvar)) =
      Semiterm.func Language.Add.add ![Semiterm.lMap (mapHom g) t, Semiterm.lMap (mapHom g) u] from rfl,
    Semiterm.lMap_func]
  congr 1
  funext j
  refine Fin.cases ?_ (fun j' => Fin.cases ?_ (fun j'' => j''.elim0) j') j <;> rfl

theorem lMap_succInd {ι ι' : Type} (g : ι → ι') {ξ : Type*} (φ : Semiformula (LXIN ι) ξ 1) :
    Semiformula.lMap (mapHom g) (succInd φ) = succInd (Semiformula.lMap (mapHom g) φ) := by
  have h0 : Semiterm.lMap (mapHom g) (((0 : ℕ) : Semiterm (LXIN ι) ξ 0)) =
      ((0 : ℕ) : Semiterm (LXIN ι') ξ 0) := lMap_mapHom_zero g
  have h1 : Semiterm.lMap (mapHom g)
      (Semiterm.Operator.Add.add.operator
        ![(#0 : Semiterm (LXIN ι) ξ 1), ((1 : ℕ) : Semiterm (LXIN ι) ξ 1)]) =
      Semiterm.Operator.Add.add.operator
        ![(#0 : Semiterm (LXIN ι') ξ 1), ((1 : ℕ) : Semiterm (LXIN ι') ξ 1)] := by
    rw [lMap_mapHom_addOp, Semiterm.lMap_bvar, lMap_mapHom_one]
  simp only [succInd, Semiformula.lMap_subst, Matrix.comp₁,
    LogicalConnective.HomClass.map_imply, Semiformula.lMap_all, h1]
  congr 2
  exact congrArg (fun x => (![x] : Fin 1 → Semiterm (LXIN ι') ξ 0)) h0

/-! ### The `PA` part translates -/

theorem mapHom_rel_eq {ι ι' : Type} (g : ι → ι') :
    (mapHom g).rel (Language.Eq.eq : (LXIN ι).Rel 2) = Language.Eq.eq := rfl

theorem eqAxiom_lMap_subset {ι ι' : Type} (g : ι → ι') :
    Semiformula.lMap (mapHom g) '' (𝗘𝗤 (LXIN ι)) ⊆ 𝗘𝗤 (LXIN ι') := by
  rintro _ ⟨σ, hσ, rfl⟩
  cases hσ with
  | refl =>
      have : Semiformula.lMap (mapHom g) (Theory.Eq.refl (LXIN ι)) = Theory.Eq.refl (LXIN ι') := by
        simp [Theory.Eq.refl, Semiformula.Operator.eq_def, mapHom_rel_eq]
      rw [this]; exact Theory.eqAxiom.refl
  | symm =>
      have : Semiformula.lMap (mapHom g) (Theory.Eq.symm (LXIN ι)) = Theory.Eq.symm (LXIN ι') := by
        simp [Theory.Eq.symm, Semiformula.Operator.eq_def, mapHom_rel_eq]
      rw [this]; exact Theory.eqAxiom.symm
  | trans =>
      have : Semiformula.lMap (mapHom g) (Theory.Eq.trans (LXIN ι)) = Theory.Eq.trans (LXIN ι') := by
        simp [Theory.Eq.trans, Semiformula.Operator.eq_def, mapHom_rel_eq]
      rw [this]; exact Theory.eqAxiom.trans
  | @funcExt k f =>
      have heqatom : ∀ (a b : Semiterm (LXIN ι) Empty (k + k)),
          Semiformula.lMap (mapHom g) (Semiformula.rel Language.Eq.eq ![a, b]) =
            Semiformula.rel Language.Eq.eq ![Semiterm.lMap (mapHom g) a, Semiterm.lMap (mapHom g) b] := by
        intro a b
        rw [Semiformula.lMap_rel]
        congr 1
        funext j
        refine Fin.cases ?_ (fun j' => Fin.cases ?_ (fun j'' => j''.elim0) j') j <;> rfl
      have hant : (Semiformula.lMap (mapHom g)) ∘
            (fun i : Fin k => Semiformula.rel Language.Eq.eq
              (![#(Fin.addCast k i), #(i.addNat k)] : Fin 2 → Semiterm (LXIN ι) Empty (k + k))) =
          fun i : Fin k => (Semiformula.rel Language.Eq.eq
              (![#(Fin.addCast k i), #(i.addNat k)] : Fin 2 → Semiterm (LXIN ι') Empty (k + k))) := by
        funext i; exact heqatom _ _
      have hcons : Semiformula.lMap (mapHom g)
          (Semiformula.rel Language.Eq.eq
            (![Semiterm.func f fun i : Fin k => #(Fin.addCast k i),
              Semiterm.func f fun i : Fin k => #(i.addNat k)] :
              Fin 2 → Semiterm (LXIN ι) Empty (k + k))) =
          (Semiformula.rel Language.Eq.eq
            (![Semiterm.func ((mapHom g).func f) fun i : Fin k => #(Fin.addCast k i),
              Semiterm.func ((mapHom g).func f) fun i : Fin k => #(i.addNat k)] :
              Fin 2 → Semiterm (LXIN ι') Empty (k + k)) :
            Semiformula (LXIN ι') Empty (k + k)) := by
        rw [Semiformula.lMap_rel, mapHom_rel_eq]
        congr 1
        funext j
        refine Fin.cases ?_ (fun j' => Fin.cases ?_ (fun j'' => j''.elim0) j') j <;>
          (try simp only [Semiterm.lMap_func]
           exact congrArg (Semiterm.func ((mapHom g).func f)) (funext fun i => rfl))
      have : Semiformula.lMap (mapHom g) (Theory.Eq.funcExt f) =
          Theory.Eq.funcExt ((mapHom g).func f) := by
        simp only [Theory.Eq.funcExt, Semiformula.lMap_allClosure,
          LogicalConnective.HomClass.map_imply, Matrix.hom_conj, Semiformula.Operator.eq_def]
        congr 1
        rw [hant]
        exact congrArg (fun X => (Matrix.conj fun i : Fin k => Semiformula.rel Language.Eq.eq
          ![#(Fin.addCast k i), #(i.addNat k)]) 🡒 X) hcons
      rw [this]; exact Theory.eqAxiom.funcExt _
  | @relExt k r =>
      have heqatom : ∀ (a b : Semiterm (LXIN ι) Empty (k + k)),
          Semiformula.lMap (mapHom g) (Semiformula.rel Language.Eq.eq ![a, b]) =
            Semiformula.rel Language.Eq.eq ![Semiterm.lMap (mapHom g) a, Semiterm.lMap (mapHom g) b] := by
        intro a b
        rw [Semiformula.lMap_rel]
        congr 1
        funext j
        refine Fin.cases ?_ (fun j' => Fin.cases ?_ (fun j'' => j''.elim0) j') j <;> rfl
      have hant : (Semiformula.lMap (mapHom g)) ∘
            (fun i : Fin k => Semiformula.rel Language.Eq.eq
              (![#(Fin.addCast k i), #(i.addNat k)] : Fin 2 → Semiterm (LXIN ι) Empty (k + k))) =
          fun i : Fin k => (Semiformula.rel Language.Eq.eq
              (![#(Fin.addCast k i), #(i.addNat k)] : Fin 2 → Semiterm (LXIN ι') Empty (k + k))) := by
        funext i; exact heqatom _ _
      have : Semiformula.lMap (mapHom g) (Theory.Eq.relExt r) =
          Theory.Eq.relExt ((mapHom g).rel r) := by
        simp only [Theory.Eq.relExt, Semiformula.lMap_allClosure,
          LogicalConnective.HomClass.map_imply, Matrix.hom_conj, Semiformula.Operator.eq_def]
        congr 1
        rw [hant]
        congr 1 <;>
          (try (rw [Semiformula.lMap_rel]
                congr 1
                funext j
                refine Fin.cases ?_ (fun j' => j'.elim0) j
                simp))
      rw [this]; exact Theory.eqAxiom.relExt _

theorem paLXIN_lMap_subset {ι ι' : Type} [DecidableEq ι] [DecidableEq ι'] (g : ι → ι') :
    Semiformula.lMap (mapHom g) '' (paLXIN ι) ⊆ paLXIN ι' := by
  rintro _ ⟨σ, hσ, rfl⟩
  rcases hσ with hσ | hσ | hσ
  · exact Or.inl (eqAxiom_lMap_subset g ⟨σ, hσ, rfl⟩)
  · obtain ⟨σ', hσ', rfl⟩ := hσ
    exact Or.inr (Or.inl ⟨σ', hσ', (lm_mapHom g σ').symm⟩)
  · obtain ⟨φ, -, rfl⟩ := hσ
    refine Or.inr (Or.inr ⟨Semiformula.lMap (mapHom g) φ, trivial, ?_⟩)
    rw [lMap_univCl, lMap_succInd]

/-! ### The induction axiom translates -/

theorem lMap_substIAt_of_levelBounded {ι ι' : Type} [DecidableEq ι] [DecidableEq ι']
    [PartialOrder ι] (g : ι → ι') (k : ι) (hk : ∀ j < k, g j ≠ g k) {ξ : Type*}
    (F : Semiformula (LXIN ι) ξ 1) :
    ∀ {n : ℕ} (φ : Semiformula (LXIN ι) ξ n), LevelBounded k φ →
      Semiformula.lMap (mapHom g) (substIAt k F φ) =
        substIAt (g k) (Semiformula.lMap (mapHom g) F) (Semiformula.lMap (mapHom g) φ)
  | _, .verum, _ => rfl
  | _, .falsum, _ => rfl
  | _, .rel (Sum.inl r) v, _ => rfl
  | _, .rel (Sum.inr IXRelN.X) v, _ => rfl
  | _, .rel (Sum.inr (IXRelN.I j)) v, hφ => by
      have hlm : Semiformula.lMap (mapHom g) (Semiformula.rel (Sum.inr (IXRelN.I j)) v) =
          Semiformula.rel (Sum.inr (IXRelN.I (g j))) (fun i => Semiterm.lMap (mapHom g) (v i)) :=
        rfl
      rw [hlm]
      by_cases hjk : j = k
      · subst hjk
        have e1 : substIAt j F (Semiformula.rel (Sum.inr (IXRelN.I j)) v) = F/[v 0] := by
          rw [substIAt]; exact dif_pos rfl
        have e2 : substIAt (g j) (Semiformula.lMap (mapHom g) F)
            (Semiformula.rel (Sum.inr (IXRelN.I (g j))) (fun i => Semiterm.lMap (mapHom g) (v i)))
            = (Semiformula.lMap (mapHom g) F)/[Semiterm.lMap (mapHom g) (v 0)] := by
          rw [substIAt]; exact dif_pos rfl
        rw [e1, e2, Semiformula.lMap_subst]
        congr 1
        funext i
        refine Fin.cases ?_ (fun i => i.elim0) i
        rfl
      · have hlt : j < k := lt_of_le_of_ne hφ hjk
        have e1 : substIAt k F (Semiformula.rel (Sum.inr (IXRelN.I j)) v) =
            Semiformula.rel (Sum.inr (IXRelN.I j)) v := by
          rw [substIAt]; exact dif_neg hjk
        have e2 : substIAt (g k) (Semiformula.lMap (mapHom g) F)
            (Semiformula.rel (Sum.inr (IXRelN.I (g j))) (fun i => Semiterm.lMap (mapHom g) (v i)))
            = Semiformula.rel (Sum.inr (IXRelN.I (g j))) (fun i => Semiterm.lMap (mapHom g) (v i)) := by
          rw [substIAt]; exact dif_neg (hk j hlt)
        rw [e1, e2, hlm]
  | _, .nrel (Sum.inl r) v, _ => rfl
  | _, .nrel (Sum.inr IXRelN.X) v, _ => rfl
  | _, .nrel (Sum.inr (IXRelN.I j)) v, hφ => by
      have hlm : Semiformula.lMap (mapHom g) (Semiformula.nrel (Sum.inr (IXRelN.I j)) v) =
          Semiformula.nrel (Sum.inr (IXRelN.I (g j))) (fun i => Semiterm.lMap (mapHom g) (v i)) :=
        rfl
      rw [hlm]
      by_cases hjk : j = k
      · subst hjk
        have e1 : substIAt j F (Semiformula.nrel (Sum.inr (IXRelN.I j)) v) = ∼(F/[v 0]) := by
          rw [substIAt]; exact dif_pos rfl
        have e2 : substIAt (g j) (Semiformula.lMap (mapHom g) F)
            (Semiformula.nrel (Sum.inr (IXRelN.I (g j))) (fun i => Semiterm.lMap (mapHom g) (v i)))
            = ∼((Semiformula.lMap (mapHom g) F)/[Semiterm.lMap (mapHom g) (v 0)]) := by
          rw [substIAt]; exact dif_pos rfl
        rw [e1, e2, LogicalConnective.HomClass.map_neg, Semiformula.lMap_subst]
        congr 2
        funext i
        refine Fin.cases ?_ (fun i => i.elim0) i
        rfl
      · have hlt : j < k := lt_of_le_of_ne hφ hjk
        have e1 : substIAt k F (Semiformula.nrel (Sum.inr (IXRelN.I j)) v) =
            Semiformula.nrel (Sum.inr (IXRelN.I j)) v := by
          rw [substIAt]; exact dif_neg hjk
        have e2 : substIAt (g k) (Semiformula.lMap (mapHom g) F)
            (Semiformula.nrel (Sum.inr (IXRelN.I (g j))) (fun i => Semiterm.lMap (mapHom g) (v i)))
            = Semiformula.nrel (Sum.inr (IXRelN.I (g j))) (fun i => Semiterm.lMap (mapHom g) (v i)) := by
          rw [substIAt]; exact dif_neg (hk j hlt)
        rw [e1, e2, hlm]
  | _, .and φ ψ, hφ => by
      show Semiformula.lMap (mapHom g) (substIAt k F φ ⋏ substIAt k F ψ) =
        substIAt (g k) (Semiformula.lMap (mapHom g) F) (Semiformula.lMap (mapHom g) φ) ⋏
          substIAt (g k) (Semiformula.lMap (mapHom g) F) (Semiformula.lMap (mapHom g) ψ)
      rw [LogicalConnective.HomClass.map_and,
        lMap_substIAt_of_levelBounded g k hk F φ hφ.1,
        lMap_substIAt_of_levelBounded g k hk F ψ hφ.2]
  | _, .or φ ψ, hφ => by
      show Semiformula.lMap (mapHom g) (substIAt k F φ ⋎ substIAt k F ψ) =
        substIAt (g k) (Semiformula.lMap (mapHom g) F) (Semiformula.lMap (mapHom g) φ) ⋎
          substIAt (g k) (Semiformula.lMap (mapHom g) F) (Semiformula.lMap (mapHom g) ψ)
      rw [LogicalConnective.HomClass.map_or,
        lMap_substIAt_of_levelBounded g k hk F φ hφ.1,
        lMap_substIAt_of_levelBounded g k hk F ψ hφ.2]
  | _, .all φ, hφ => by
      show Semiformula.lMap (mapHom g) (∀¹ substIAt k F φ) =
        ∀¹ substIAt (g k) (Semiformula.lMap (mapHom g) F) (Semiformula.lMap (mapHom g) φ)
      rw [Semiformula.lMap_all, lMap_substIAt_of_levelBounded g k hk F φ hφ]
  | _, .exs φ, hφ => by
      show Semiformula.lMap (mapHom g) (∃¹ substIAt k F φ) =
        ∃¹ substIAt (g k) (Semiformula.lMap (mapHom g) F) (Semiformula.lMap (mapHom g) φ)
      rw [Semiformula.lMap_exs, lMap_substIAt_of_levelBounded g k hk F φ hφ]

/-- `LevelBounded` is invariant under an arbitrary term rewriting (own copy: `LowerBound.lean`
and `Theorem.lean` both bind the name `levelBounded_rew`, at incompatible types — `Fin n`-only
vs the general `ι` version this file needs — so a fresh name avoids the overload clash). -/
theorem levelBounded_rewOwn {ι : Type} [PartialOrder ι] (k : ι) {ξ₁ ξ₂ : Type*} :
    ∀ {n₁ n₂ : ℕ} (ω : Rew (LXIN ι) ξ₁ n₁ ξ₂ n₂) (φ : Semiformula (LXIN ι) ξ₁ n₁),
      LevelBounded k φ → LevelBounded k (ω ▹ φ)
  | _, _, _, .verum, _ => trivial
  | _, _, _, .falsum, _ => trivial
  | _, _, _, .rel (Sum.inl _) _, _ => trivial
  | _, _, _, .rel (Sum.inr IXRelN.X) _, _ => trivial
  | _, _, _, .rel (Sum.inr (IXRelN.I _)) _, h => h
  | _, _, _, .nrel (Sum.inl _) _, _ => trivial
  | _, _, _, .nrel (Sum.inr IXRelN.X) _, _ => trivial
  | _, _, _, .nrel (Sum.inr (IXRelN.I _)) _, h => h
  | _, _, ω, .and φ ψ, h => ⟨levelBounded_rewOwn k ω φ h.1, levelBounded_rewOwn k ω ψ h.2⟩
  | _, _, ω, .or φ ψ, h => ⟨levelBounded_rewOwn k ω φ h.1, levelBounded_rewOwn k ω ψ h.2⟩
  | _, _, ω, .all φ, h => levelBounded_rewOwn k ω.q φ h
  | _, _, ω, .exs φ, h => levelBounded_rewOwn k ω.q φ h

theorem lMap_opAt {ι ι' : Type} [DecidableEq ι] [DecidableEq ι'] [PartialOrder ι]
    (g : ι → ι') (k : ι) (hk : ∀ j < k, g j ≠ g k) {A : Semisentence (LXIN ι) 1}
    (hA : LevelBounded k (Rewriting.emb A : Semiformula (LXIN ι) ℕ 1))
    (F : Semiformula (LXIN ι) ℕ 1) :
    Semiformula.lMap (mapHom g) (opAt k A F) =
      opAt (g k) (Semiformula.lMap (mapHom g) A) (Semiformula.lMap (mapHom g) F) := by
  show Semiformula.lMap (mapHom g) (substIAt k F (Rewriting.emb A)) =
    substIAt (g k) (Semiformula.lMap (mapHom g) F) (Rewriting.emb (Semiformula.lMap (mapHom g) A))
  rw [lMap_substIAt_of_levelBounded g k hk F _ hA, Semiformula.lMap_emb]

theorem lMap_indAxAt {ι ι' : Type} [DecidableEq ι] [DecidableEq ι'] [PartialOrder ι]
    (g : ι → ι') (k : ι) (hk : ∀ j < k, g j ≠ g k) {A : Semisentence (LXIN ι) 1}
    (hA : LevelBounded k (Rewriting.emb A : Semiformula (LXIN ι) ℕ 1))
    (F : Semiformula (LXIN ι) ℕ 1) :
    Semiformula.lMap (mapHom g) (indAxAt k A F) =
      indAxAt (g k) (Semiformula.lMap (mapHom g) A) (Semiformula.lMap (mapHom g) F) := by
  show Semiformula.lMap (mapHom g)
      (Semiformula.univCl ((∀¹ (opAt k A F 🡒 F)) 🡒 ∀¹ (Iat k #0 🡒 F))) =
    Semiformula.univCl ((∀¹ (opAt (g k) (Semiformula.lMap (mapHom g) A)
        (Semiformula.lMap (mapHom g) F) 🡒 Semiformula.lMap (mapHom g) F)) 🡒
      ∀¹ (Iat (g k) #0 🡒 Semiformula.lMap (mapHom g) F))
  rw [lMap_univCl, LogicalConnective.HomClass.map_imply, Semiformula.lMap_all,
    LogicalConnective.HomClass.map_imply, lMap_opAt g k hk hA F, Semiformula.lMap_all,
    LogicalConnective.HomClass.map_imply, lMap_Iat, Semiterm.lMap_bvar]

/-! ### The translation-of-derivations lemma -/

theorem theory_proof_lMap {L₁ L₂ : Language} (Φ : L₁ →ᵥ L₂) {T : Theory L₁} {σ : Sentence L₁}
    (h : T ⊢ σ) : Theory.lMap Φ T ⊢ Semiformula.lMap Φ σ := by
  rw [Theory.Proof.provable_iff] at h
  obtain ⟨Γ, hΓ, ⟨d⟩⟩ := h
  rw [Theory.Proof.provable_iff]
  refine ⟨Γ.map (Semiformula.lMap Φ), ?_, ⟨?_⟩⟩
  · rintro ψ hψ
    obtain ⟨ψ', hψ', rfl⟩ := List.mem_map.mp hψ
    exact ⟨ψ', hΓ ψ' hψ', rfl⟩
  · have d' := Derivation.lMap Φ d
    simp only [List.map_cons] at d'
    have hemb : ∀ Γ' : List (Sentence L₁),
        (Sequent.embed Γ').map (Semiformula.lMap Φ) = Sequent.embed (Γ'.map (Semiformula.lMap Φ)) := by
      intro Γ'
      simp only [Sequent.embed, List.map_map]
      congr 1
      funext ψ
      exact Semiformula.lMap_emb ψ
    have hneg : ((∼Sequent.embed Γ : Sequent L₁)).map (Semiformula.lMap Φ) =
        (∼Sequent.embed (Γ.map (Semiformula.lMap Φ)) : Sequent L₂) := by
      rw [List.map_tilde, hemb]
    rw [Semiformula.lMap_emb, hneg] at d'
    exact d'

/-! ### The retraction, assembled -/

theorem idseq_lMap_subset (F : OrderFormulas) (m : ℕ) (hm : 0 < m) :
    Theory.lMap (retr m hm) (IDseq (Upper.WFormsOmega F) m) ⊆ IDn m (WForms F m) := by
  rintro _ ⟨σ, hσ, rfl⟩
  rcases hσ with hσ | hσ
  · exact paLXIN_subset_ID _ (paLXIN_lMap_subset (retrFun m hm) ⟨σ, hσ, rfl⟩)
  · simp only [Set.mem_iUnion] at hσ
    obtain ⟨k, hkm, hσ⟩ := hσ
    have hkm' : k < m := hkm
    have hAtrans : Semiformula.lMap (mapHom (retrFun m hm)) (Upper.WFormsOmega F k) =
        WForms F m ⟨k, hkm'⟩ := by
      show Semiformula.lMap (mapHom (retrFun m hm)) (wForm F id k) =
        wForm F (ixFin (Fin.pos (⟨k, hkm'⟩ : Fin m))) k
      rw [lMap_wForm]
      apply wForm_congr
      intro i hi
      have hi' : i < m := by omega
      show retrFun m hm i = ixFin (Fin.pos (⟨k, hkm'⟩ : Fin m)) i
      rw [retrFun_eq_of_lt hm hi']
      show (⟨i, hi'⟩ : Fin m) = ⟨i % m, Nat.mod_lt i (Fin.pos (⟨k, hkm'⟩ : Fin m))⟩
      congr 1
      exact (Nat.mod_eq_of_lt hi').symm
    have hkinj : ∀ j < k, retrFun m hm j ≠ retrFun m hm k :=
      fun j hj => retrFun_ne_of_lt hm (by omega) hkm' (by omega)
    have hAbounded :
        LevelBounded k (Rewriting.emb (Upper.WFormsOmega F k) : Semiformula LXIomega ℕ 1) :=
      levelBounded_rewOwn k Rew.emb (Upper.WFormsOmega F k) (wFormsOmega_levelBounded F k)
    rcases hσ with hσ | ⟨G, hσ⟩
    · subst hσ
      show Semiformula.lMap (mapHom (retrFun m hm)) (closureAxAt k (Upper.WFormsOmega F k)) ∈
        IDn m (WForms F m)
      rw [lMap_closureAxAt, hAtrans, retrFun_eq_of_lt hm hkm']
      exact closureAxAt_mem_ID (WForms F m) (⟨k, hkm'⟩ : Fin m)
    · subst hσ
      show Semiformula.lMap (mapHom (retrFun m hm)) (indAxAt k (Upper.WFormsOmega F k) G) ∈
        IDn m (WForms F m)
      rw [lMap_indAxAt (retrFun m hm) k hkinj hAbounded G, hAtrans, retrFun_eq_of_lt hm hkm']
      exact indAxAt_mem_ID (WForms F m) (⟨k, hkm'⟩ : Fin m) _

theorem retraction_step (F : OrderFormulas) (a : ThetaWNoteD) (m : ℕ) (hm : 0 < m)
    (h : IDseq (Upper.WFormsOmega F) m ⊢ tiUptoSentence F ℕ a) :
    IDn m (WForms F m) ⊢ tiUptoSentence F (Fin m) a := by
  have htrans := theory_proof_lMap (retr m hm) h
  have heq : Semiformula.lMap (retr m hm) (tiUptoSentence F ℕ a) = tiUptoSentence F (Fin m) a :=
    lMap_tiUptoSentence (retrFun m hm) F a
  rw [heq] at htrans
  exact (Entailment.WeakerThan.ofSubset (idseq_lMap_subset F m hm)).wk htrans

/-- **`IDseqToIDn orderFormulas (Omega 0)`** — the one further open link `idlt_theorem` needs. -/
theorem idseq_to_idn (hyps1 : EmbedHyps (WForms orderFormulas 1))
    (hcol1 : CollapseCorollary (Nat.zero_lt_one)) :
    IDseqToIDn orderFormulas (ThetaWNoteD.Omega 0) := by
  intro m h
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · exfalso
    subst hm0
    have hsub : IDseq (Upper.WFormsOmega orderFormulas) 0 ⊆
        IDseq (Upper.WFormsOmega orderFormulas) 1 := IDseq_mono _ (by omega)
    have h1 : IDseq (Upper.WFormsOmega orderFormulas) 1 ⊢
        tiUptoSentence orderFormulas ℕ (ThetaWNoteD.Omega 0) :=
      (Entailment.WeakerThan.ofSubset hsub).wk h
    exact idn_lower_bound Nat.zero_lt_one hyps1 hcol1
      (retraction_step orderFormulas (ThetaWNoteD.Omega 0) 1 Nat.zero_lt_one h1)
  · exact ⟨hmpos, retraction_step orderFormulas (ThetaWNoteD.Omega 0) m hmpos h⟩

example (hyps : ∀ m : ℕ, 0 < m → EmbedHyps (WForms orderFormulas m))
    (hcol : ∀ (m : ℕ) (hm : 0 < m), CollapseCorollary (n := m) hm) :
    (∀ a : ThetaWNoteD, a.1 < ThetaWTerm.Omega 0 →
        IDlt (Upper.WFormsOmega orderFormulas) ⊢ tiUptoSentence orderFormulas ℕ a) ∧
      ¬ IDlt (Upper.WFormsOmega orderFormulas) ⊢
        tiUptoSentence orderFormulas ℕ (ThetaWNoteD.Omega 0) :=
  idlt_theorem hyps hcol
    (idseq_to_idn (hyps 1 Nat.zero_lt_one) (hcol 1 Nat.zero_lt_one))

end IDn

end OrdinalAnalysis
