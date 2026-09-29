/-
  The producer of the `Cong` instances of `IDw/Transfer.lean`.

  For a positive form `A : FormJ` (`PositiveP A`), a closed `t` and a level `k`, the infinitary
  unfolding `unfoldW A k (StageAt.top k) t` (`P ↦ I_k`, `Q ↦ Jlev k`) and the embedded finitary
  instance `embInst (Jat #1 #0) k A t` (the `y := k̄`, `x := t` instance of the body of
  `Rewriting.emb (embK (closureAxJ A))`: `P ↦ Jlev ⊤ (k̄,·)`, `Q(a,b) ↦ a < k̄ ∧ Jlev ⊤ (a,b)`) are
  congruent up to the atom pairs of T1-T4, in both directions:

      cong_unfold_fwd : Cong (OkFwd k) (cdepth A) (unfoldW A k top t) (embInst (Jat #1 #0) k A t)
      cong_unfold_bwd : Cong (OkBwd k) (cdepth A) (embInst (Jat #1 #0) k A t) (unfoldW A k top t)

  and, composed with `transfer5_fwd/bwd` (`transfer_unfold_fwd/bwd`), `⊢ ¬B, B'` resp. `⊢ ¬B', B`
  at height `Ω_{k+1} ⊕ (4 + 2 · cdepth A)`.  The core is `cong_AAt`, a structural induction on a
  schema formula `φ : Semiformula LForm Empty n`, generalising over closed instantiations
  `ρ : Fin n → SyntacticTerm` and a level term `Y` with `ρ(Y) = k̄` (the `Rew.bShift`-threaded
  level of `AAt`), for an arbitrary own-place formula `F`, stage bound `g` and atom relation
  `Ok`; `cong_unfold` is its `unfoldW`/`embInst` form (also used, with `Ok` built from the
  identity lemma at the formula `F`, for the induction axiom `indAxJ A F`, whose body is
  `AAt F #1 (Rewriting.emb A)`).

  Contents.

    `cdepth`                                    the `Cong` index of a schema formula
    `Cong.mono`, `Cong.symm`, `okBwd_iff`, `cong_bwd_of_fwd`
    `lMap_embedW_termCast`, `emb_lMap_term`     the two term compilations agree
    `subst_q_inst`, `subst_cons_bShift`, ...    closed instances of a substituted body
    `cong_AAt`                                  the producer (generic)
    `embInst`, `cong_unfold`, `cong_unfold_fwd`, `cong_unfold_bwd`
    `embInst_closure`, `closure_axiom_inst`     the closure-axiom presentation
    `transfer_unfold_fwd`, `transfer_unfold_bwd`
-/
import OrdinalAnalysis.IDw.Transfer
import OrdinalAnalysis.IDw.NumSubst
import OrdinalAnalysis.IDw.Sound

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Transfer

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting

/-! ### The connective/quantifier depth of a schema formula -/

/-- The depth index of `Cong`: `0` on atoms, `max + 1` on `∧`, `∨`, `+ 1` on `∀`, `∃`. -/
def cdepth {ξ : Type*} : {n : ℕ} → Semiformula LForm ξ n → ℕ
  | _, .verum => 0
  | _, .falsum => 0
  | _, .rel _ _ => 0
  | _, .nrel _ _ => 0
  | _, .and φ ψ => max (cdepth φ) (cdepth ψ) + 1
  | _, .or φ ψ => max (cdepth φ) (cdepth ψ) + 1
  | _, .all φ => cdepth φ + 1
  | _, .exs φ => cdepth φ + 1

/-! ### `Cong` is symmetric and monotone in `Ok` -/

theorem Cong.mono {Ok Ok' : Proposition LIinfW → Proposition LIinfW → Prop}
    (h : ∀ B B', Ok B B' → Ok' B B') {c : ℕ} {B B' : Proposition LIinfW}
    (hc : Cong Ok c B B') : Cong Ok' c B B' := by
  induction hc with
  | atom h' => exact .atom (h _ _ h')
  | verum => exact .verum
  | falsum => exact .falsum
  | and _ _ ih₀ ih₁ => exact .and ih₀ ih₁
  | or _ _ ih₀ ih₁ => exact .or ih₀ ih₁
  | all _ ih => exact .all ih
  | exs _ ih => exact .exs ih

theorem Cong.symm {Ok : Proposition LIinfW → Proposition LIinfW → Prop} {c : ℕ}
    {B B' : Proposition LIinfW} (hc : Cong Ok c B B') : Cong (fun x y => Ok y x) c B' B := by
  induction hc with
  | atom h' => exact .atom h'
  | verum => exact .verum
  | falsum => exact .falsum
  | and _ _ ih₀ ih₁ => exact .and ih₀ ih₁
  | or _ _ ih₀ ih₁ => exact .or ih₀ ih₁
  | all _ ih => exact .all ih
  | exs _ ih => exact .exs ih

theorem okBwd_iff (k : ℕ) (B B' : Proposition LIinfW) : OkBwd k B B' ↔ OkFwd k B' B := by
  constructor
  · rintro (⟨h, rfl⟩ | ⟨s, hs, rfl, rfl⟩ | ⟨j, a, hj, ha, rfl, rfl⟩ | ⟨j, a, hj, ha, rfl, rfl⟩)
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr (Or.inl ⟨s, hs, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨j, a, hj, ha, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨j, a, hj, ha, rfl, rfl⟩))
  · rintro (⟨h, rfl⟩ | ⟨s, hs, rfl, rfl⟩ | ⟨j, a, hj, ha, rfl, rfl⟩ | ⟨j, a, hj, ha, rfl, rfl⟩)
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr (Or.inl ⟨s, hs, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨j, a, hj, ha, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨j, a, hj, ha, rfl, rfl⟩))

/-- The `OkBwd`-congruence from the `OkFwd`-congruence, read backwards. -/
theorem cong_bwd_of_fwd {k c : ℕ} {B B' : Proposition LIinfW} (h : Cong (OkFwd k) c B B') :
    Cong (OkBwd k) c B' B :=
  h.symm.mono fun _ _ h' => (okBwd_iff k _ _).mpr h'

/-! ### Terms: the two compilations agree -/

section Terms

theorem lMap_embedW_termCast {ξ' : Type*} {m : ℕ} (k : ℕ) (g : StageAt k)
    (t : Semiterm LForm ξ' m) :
    Semiterm.lMap embedW (termCast t) = Semiterm.lMap (formHomAt k g) t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih =>
    have hf : embedW.func (homLFormLXJ.func f) = (formHomAt k g).func f := by
      rcases f with f | f
      · rfl
      · exact PEmpty.elim f
    simp only [termCast, Semiterm.lMap_func] at ih ⊢
    rw [hf]
    congr 1
    funext i
    exact ih i

theorem lMap_emb_term {ξ' : Type*} {m : ℕ} (Φ : LForm →ᵥ LIinfW) (t : Semiterm LForm Empty m) :
    Semiterm.lMap Φ (Rew.emb t : Semiterm LForm ξ' m) = Rew.emb (Semiterm.lMap Φ t) := by
  induction t with
  | bvar x => rfl
  | fvar x => exact x.elim
  | func f v ih =>
    simp only [Rew.func, Semiterm.lMap_func]
    congr 1
    funext i
    exact ih i

/-- The source term `emb (lMap (formHomAt k g) t)` is the embedding of the cast target term. -/
theorem emb_lMap_term (k : ℕ) (g : StageAt k) {m : ℕ} (t : Semiterm LForm Empty m) :
    (Rew.emb (Semiterm.lMap (formHomAt k g) t) : Semiterm LIinfW ℕ m) =
      Semiterm.lMap embedW (termCast (Rew.emb t : Semiterm LForm ℕ m)) := by
  rw [lMap_embedW_termCast k g, lMap_emb_term]

end Terms

/-! ### Closed instances, and the atoms of the two sides -/

section Instances

theorem freeVariables_subst_emb {m : ℕ} (ρ : Fin m → SyntacticTerm LIinfW)
    (hρ : ∀ i, (ρ i).freeVariables = ∅) (u : Semiterm LIinfW Empty m) :
    (Rew.subst ρ (Rew.emb u : Semiterm LIinfW ℕ m)).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hx' : (Rew.subst ρ (Rew.emb u : Semiterm LIinfW ℕ m)).FVar? x := hx
  rcases Semiterm.fvar?_rew hx' with ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ (ρ i).freeVariables := by
      rw [Rew.subst_bvar] at hi
      exact hi
    rw [hρ i] at hi'
    exact Finset.notMem_empty x hi'
  · have hz' : z ∈ (Rew.emb u : Semiterm LIinfW ℕ m).freeVariables := hz
    simp at hz'

/-- Instantiating the first bound variable of a substituted body: `(ρ.q ▹ ψ)/[a] = (a :> ρ) ▹ ψ`. -/
theorem subst_q_inst {m : ℕ} (ρ : Fin m → SyntacticTerm LIinfW) (a : SyntacticTerm LIinfW)
    (ψ : Semiformula LIinfW ℕ (m + 1)) :
    ((Rew.subst ρ).q ▹ ψ)/[a] = Rew.subst (a :> ρ) ▹ ψ := by
  have hc : (Rew.subst ![a] : Rew LIinfW ℕ 1 ℕ 0).comp (Rew.subst ρ).q =
      Rew.subst (a :> ρ) := by
    refine Rew.ext _ _ ?_ ?_
    · intro x
      refine Fin.cases ?_ (fun i => ?_) x
      · simp [Rew.comp_app]
      · simp [Rew.comp_app]
    · intro x; simp [Rew.comp_app]
  show Rew.subst ![a] ▹ ((Rew.subst ρ).q ▹ ψ) = _
  rw [← TransitiveRewriting.comp_app, hc]

theorem subst_cons_bShift {m : ℕ} (a : SyntacticTerm LIinfW) (ρ : Fin m → SyntacticTerm LIinfW)
    (u : Semiterm LIinfW ℕ m) : Rew.subst (a :> ρ) (Rew.bShift u) = Rew.subst ρ u := by
  have hc : (Rew.subst (a :> ρ) : Rew LIinfW ℕ (m + 1) ℕ 0).comp Rew.bShift = Rew.subst ρ := by
    ext x <;> simp [Rew.comp_app]
  rw [← Rew.comp_app, hc]

theorem emb_all' {L : Language} {ξ : Type*} {n : ℕ} (φ : Semiformula L Empty (n + 1)) :
    (Rewriting.emb (∀¹ φ) : Semiformula L ξ n) = ∀¹ (Rewriting.emb φ) := by
  show Rew.emb ▹ (∀¹ φ) = ∀¹ (Rew.emb ▹ φ)
  rw [Rewriting.app_all, Rew.q_emb]

theorem emb_exs' {L : Language} {ξ : Type*} {n : ℕ} (φ : Semiformula L Empty (n + 1)) :
    (Rewriting.emb (∃¹ φ) : Semiformula L ξ n) = ∃¹ (Rewriting.emb φ) := by
  show Rew.emb ▹ (∃¹ φ) = ∃¹ (Rew.emb ▹ φ)
  rw [Rewriting.app_exs, Rew.q_emb]

theorem embK_ltAt {ξ : Type*} {m : ℕ} (s t : Semiterm LXJ ξ m) :
    embK (ltAt s t) = ltW (embT s) (embT t) := by
  show Semiformula.rel (Sum.inl Language.LT.lt : LIinfW.Rel 2)
      (fun i => Semiterm.lMap embedW (![s, t] i)) = _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem rew_ltW {ξ ζ : Type*} {n₁ n₂ : ℕ} (ω : Rew LIinfW ξ n₁ ζ n₂) (s t : Semiterm LIinfW ξ n₁) :
    ω ▹ ltW s t = ltW (ω s) (ω t) :=
  Semiformula.rew_rel2 ω

theorem rew_jlevAt {ξ ζ : Type*} {n₁ n₂ : ℕ} (ω : Rew LIinfW ξ n₁ ζ n₂) (ℓ : WithTop ℕ)
    (s t : Semiterm LIinfW ξ n₁) : ω ▹ jlevAt ℓ s t = jlevAt ℓ (ω s) (ω t) :=
  Semiformula.rew_rel2 ω

end Instances

/-! ### The producer: the unfolding at level `k` is congruent to the embedded finitary instance -/

section Producer

variable (k : ℕ) (g : StageAt k)

/-- **The congruence between the two compilations of a positive schema formula.**  For `φ` a
subformula of the form `A` (`PositiveP φ`), a closed instantiation `ρ` of its bound variables
and a level term `Y` with `ρ(Y) = k̄`, the unfolding at level `k` (`P ↦ I_k^{≺g}`, `Q ↦ Jlev k`)
and the embedded finitary compilation `AAt F Y` (`P ↦ F(·, Y)`, `Q(a,b) ↦ a < Y ∧ J(a,b)`, then
`J ↦ Jlev ⊤`) are `Cong`ruent, for any `Ok` containing the four atom pairs. -/
theorem cong_AAt {Ok : Proposition LIinfW → Proposition LIinfW → Prop}
    (F : Semiformula LXJ ℕ 2)
    (hAr : ∀ B, IsArithLit B → Ok B B)
    (hP : ∀ s : SyntacticTerm LIinfW, s.freeVariables = ∅ →
      Ok (stageAt ⟨k, g⟩ s) ((embK F)/[s, numI k]))
    (hQ : ∀ j a : SyntacticTerm LIinfW, j.freeVariables = ∅ → a.freeVariables = ∅ →
      Ok (jlevAt (k : WithTop ℕ) j a) (qTop k j a))
    (hNQ : ∀ j a : SyntacticTerm LIinfW, j.freeVariables = ∅ → a.freeVariables = ∅ →
      Ok (njlevAt (k : WithTop ℕ) j a) (∼(qTop k j a))) :
    ∀ {n : ℕ} (φ : Semiformula LForm Empty n), PositiveP φ →
      ∀ (ρ : Fin n → SyntacticTerm LIinfW), (∀ i, (ρ i).freeVariables = ∅) →
      ∀ (Y : Semiterm LXJ ℕ n), Rew.subst ρ (Semiterm.lMap embedW Y) = numI k →
      Cong Ok (cdepth φ)
        (Rew.subst ρ ▹
          (Rewriting.emb (Semiformula.lMap (formHomAt k g) φ) : Semiformula LIinfW ℕ n))
        (Rew.subst ρ ▹ embK (AAt F Y (Rewriting.emb φ : Semiformula LForm ℕ n))) := by
  intro n φ
  induction φ using Semiformula.rec' with
  | @hverum n => intro _ ρ _ Y _; exact Cong.verum
  | @hfalsum n => intro _ ρ _ Y _; exact Cong.falsum
  | @hand n φ ψ ihφ ihψ =>
    intro hpos ρ hρ Y hY
    exact Cong.and (ihφ hpos.1 ρ hρ Y hY) (ihψ hpos.2 ρ hρ Y hY)
  | @hor n φ ψ ihφ ihψ =>
    intro hpos ρ hρ Y hY
    exact Cong.or (ihφ hpos.1 ρ hρ Y hY) (ihψ hpos.2 ρ hρ Y hY)
  | @hall n φ ih =>
    intro hpos ρ hρ Y hY
    have e1 : (Rew.subst ρ ▹
          (Rewriting.emb (Semiformula.lMap (formHomAt k g) (∀¹ φ)) : Semiformula LIinfW ℕ n)) =
        ∀¹ ((Rew.subst ρ).q ▹
          (Rewriting.emb (Semiformula.lMap (formHomAt k g) φ) : Semiformula LIinfW ℕ (n + 1))) := by
      rw [Semiformula.lMap_all, emb_all', Rewriting.app_all]
    have e2 : (Rew.subst ρ ▹ embK (AAt F Y (Rewriting.emb (∀¹ φ) : Semiformula LForm ℕ n))) =
        ∀¹ ((Rew.subst ρ).q ▹
          embK (AAt F (Rew.bShift Y) (Rewriting.emb φ : Semiformula LForm ℕ (n + 1)))) := by
      rw [emb_all']
      show Rew.subst ρ ▹ embK (∀¹ AAt F (Rew.bShift Y) (Rewriting.emb φ)) = _
      rw [embK_all, Rewriting.app_all]
    rw [e1, e2]
    refine Cong.all fun m => ?_
    rw [subst_q_inst, subst_q_inst]
    refine ih hpos (numI m :> ρ) ?_ (Rew.bShift Y) ?_
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact numI_freeVariables m
      · exact hρ i
    · rw [Semiterm.lMap_bShift, subst_cons_bShift]; exact hY
  | @hexs n φ ih =>
    intro hpos ρ hρ Y hY
    have e1 : (Rew.subst ρ ▹
          (Rewriting.emb (Semiformula.lMap (formHomAt k g) (∃¹ φ)) : Semiformula LIinfW ℕ n)) =
        ∃¹ ((Rew.subst ρ).q ▹
          (Rewriting.emb (Semiformula.lMap (formHomAt k g) φ) : Semiformula LIinfW ℕ (n + 1))) := by
      rw [Semiformula.lMap_exs, emb_exs', Rewriting.app_exs]
    have e2 : (Rew.subst ρ ▹ embK (AAt F Y (Rewriting.emb (∃¹ φ) : Semiformula LForm ℕ n))) =
        ∃¹ ((Rew.subst ρ).q ▹
          embK (AAt F (Rew.bShift Y) (Rewriting.emb φ : Semiformula LForm ℕ (n + 1)))) := by
      rw [emb_exs']
      show Rew.subst ρ ▹ embK (∃¹ AAt F (Rew.bShift Y) (Rewriting.emb φ)) = _
      rw [embK_exs, Rewriting.app_exs]
    rw [e1, e2]
    refine Cong.exs fun m => ?_
    rw [subst_q_inst, subst_q_inst]
    refine ih hpos (numI m :> ρ) ?_ (Rew.bShift Y) ?_
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact numI_freeVariables m
      · exact hρ i
    · rw [Semiterm.lMap_bShift, subst_cons_bShift]; exact hY
  | @hrel n _ r v =>
    rcases r with r | r
    · intro _ ρ hρ Y hY
      have hv : ∀ i, (Rew.subst ρ
          (Rew.emb (Semiterm.lMap (formHomAt k g) (v i)) : Semiterm LIinfW ℕ n)).freeVariables
            = ∅ := fun i => freeVariables_subst_emb ρ hρ _
      have e : (Rew.subst ρ ▹ embK (AAt F Y
            (Rewriting.emb (Semiformula.rel (Sum.inl r : LForm.Rel _) v) :
              Semiformula LForm ℕ n))) =
          Rew.subst ρ ▹
            (Rewriting.emb (Semiformula.lMap (formHomAt k g)
              (Semiformula.rel (Sum.inl r : LForm.Rel _) v)) : Semiformula LIinfW ℕ n) := by
        show Semiformula.rel (Sum.inl r : LIinfW.Rel _)
            (fun i => Rew.subst ρ (Semiterm.lMap embedW (termCast (Rew.emb (v i))))) =
          Semiformula.rel (Sum.inl r : LIinfW.Rel _)
            (fun i => Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v i))))
        congr 1
        funext i
        rw [emb_lMap_term]
      rw [e]
      exact Cong.atom (hAr _ ⟨_, r, fun i => Rew.subst ρ
        (Rew.emb (Semiterm.lMap (formHomAt k g) (v i))), Or.inl rfl, hv⟩)
    · cases r with
      | P =>
        intro _ ρ hρ Y hY
        have hs := freeVariables_subst_emb ρ hρ (Semiterm.lMap (formHomAt k g) (v 0))
        have e1 : (Rew.subst ρ ▹
            (Rewriting.emb (Semiformula.lMap (formHomAt k g)
              (Semiformula.rel (Sum.inr PQRel.P) v)) : Semiformula LIinfW ℕ n)) =
            stageAt ⟨k, g⟩ (Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v 0)))) := by
          show Semiformula.rel (Sum.inr (IInfRelW.stage ⟨k, g⟩))
            (fun i => Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v i)))) = _
          congr 1
          funext i
          obtain rfl := Subsingleton.elim i 0
          rfl
        have e2 : (Rew.subst ρ ▹ embK (AAt F Y
            (Rewriting.emb (Semiformula.rel (Sum.inr PQRel.P) v) : Semiformula LForm ℕ n))) =
            (embK F)/[Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v 0))), numI k] := by
          show Rew.subst ρ ▹ embK (F/[termCast (Rew.emb (v 0)), Y]) = _
          rw [show F/[termCast (Rew.emb (v 0)), Y] = F ⇜ ![termCast (Rew.emb (v 0)), Y] from rfl,
            embK_subst]
          show Rew.subst ρ ▹ (Rew.subst _ ▹ embK F) = Rew.subst _ ▹ embK F
          rw [← TransitiveRewriting.comp_app, Rew.subst_comp_subst]
          refine congrArg (fun w => Rew.subst w ▹ embK F) ?_
          funext i
          fin_cases i
          · show Rew.subst ρ (Semiterm.lMap embedW (termCast (Rew.emb (v 0)))) =
              Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v 0)))
            rw [emb_lMap_term k g]
          · exact hY
        rw [e1, e2]
        exact Cong.atom (hP _ hs)
      | Q =>
        intro _ ρ hρ Y hY
        have hj := freeVariables_subst_emb ρ hρ (Semiterm.lMap (formHomAt k g) (v 0))
        have ha := freeVariables_subst_emb ρ hρ (Semiterm.lMap (formHomAt k g) (v 1))
        have e1 : (Rew.subst ρ ▹
            (Rewriting.emb (Semiformula.lMap (formHomAt k g)
              (Semiformula.rel (Sum.inr PQRel.Q) v)) : Semiformula LIinfW ℕ n)) =
            jlevAt (k : WithTop ℕ) (Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v 0))))
              (Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v 1)))) := by
          show Semiformula.rel (Sum.inr (IInfRelW.jlev (k : WithTop ℕ)))
            (fun i => Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v i)))) = _
          congr 1
          funext i
          fin_cases i <;> rfl
        have e2 : (Rew.subst ρ ▹ embK (AAt F Y
            (Rewriting.emb (Semiformula.rel (Sum.inr PQRel.Q) v) : Semiformula LForm ℕ n))) =
            qTop k (Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v 0))))
              (Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v 1)))) := by
          show Rew.subst ρ ▹ embK (ltAt (termCast (Rew.emb (v 0))) Y ⋏
            Jat (termCast (Rew.emb (v 0))) (termCast (Rew.emb (v 1)))) = _
          rw [embK_and, embK_ltAt, embK_Jat, LogicalConnective.HomClass.map_and, rew_ltW, rew_jlevAt, hY]
          show ltW _ _ ⋏ jlevAt ⊤ _ _ = ltW _ _ ⋏ jlevAt ⊤ _ _
          rw [show embT (termCast (Rew.emb (v 0)) : Semiterm LXJ ℕ n) =
              Semiterm.lMap embedW (termCast (Rew.emb (v 0))) from rfl,
            show embT (termCast (Rew.emb (v 1)) : Semiterm LXJ ℕ n) =
              Semiterm.lMap embedW (termCast (Rew.emb (v 1))) from rfl,
            ← emb_lMap_term k g, ← emb_lMap_term k g]
        rw [e1, e2]
        exact Cong.atom (hQ _ _ hj ha)
  | @hnrel n _ r v =>
    rcases r with r | r
    · intro _ ρ hρ Y hY
      have hv : ∀ i, (Rew.subst ρ
          (Rew.emb (Semiterm.lMap (formHomAt k g) (v i)) : Semiterm LIinfW ℕ n)).freeVariables
            = ∅ := fun i => freeVariables_subst_emb ρ hρ _
      have e : (Rew.subst ρ ▹ embK (AAt F Y
            (Rewriting.emb (Semiformula.nrel (Sum.inl r : LForm.Rel _) v) :
              Semiformula LForm ℕ n))) =
          Rew.subst ρ ▹
            (Rewriting.emb (Semiformula.lMap (formHomAt k g)
              (Semiformula.nrel (Sum.inl r : LForm.Rel _) v)) : Semiformula LIinfW ℕ n) := by
        show Semiformula.nrel (Sum.inl r : LIinfW.Rel _)
            (fun i => Rew.subst ρ (Semiterm.lMap embedW (termCast (Rew.emb (v i))))) =
          Semiformula.nrel (Sum.inl r : LIinfW.Rel _)
            (fun i => Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v i))))
        congr 1
        funext i
        rw [emb_lMap_term]
      rw [e]
      exact Cong.atom (hAr _ ⟨_, r, fun i => Rew.subst ρ
        (Rew.emb (Semiterm.lMap (formHomAt k g) (v i))), Or.inr rfl, hv⟩)
    · cases r with
      | P => intro hpos; exact hpos.elim
      | Q =>
        intro _ ρ hρ Y hY
        have hj := freeVariables_subst_emb ρ hρ (Semiterm.lMap (formHomAt k g) (v 0))
        have ha := freeVariables_subst_emb ρ hρ (Semiterm.lMap (formHomAt k g) (v 1))
        have e1 : (Rew.subst ρ ▹
            (Rewriting.emb (Semiformula.lMap (formHomAt k g)
              (Semiformula.nrel (Sum.inr PQRel.Q) v)) : Semiformula LIinfW ℕ n)) =
            njlevAt (k : WithTop ℕ) (Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v 0))))
              (Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v 1)))) := by
          show Semiformula.nrel (Sum.inr (IInfRelW.jlev (k : WithTop ℕ)))
            (fun i => Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v i)))) = _
          congr 1
          funext i
          fin_cases i <;> rfl
        have e2 : (Rew.subst ρ ▹ embK (AAt F Y
            (Rewriting.emb (Semiformula.nrel (Sum.inr PQRel.Q) v) : Semiformula LForm ℕ n))) =
            ∼(qTop k (Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v 0))))
              (Rew.subst ρ (Rew.emb (Semiterm.lMap (formHomAt k g) (v 1))))) := by
          show Rew.subst ρ ▹ embK (∼(ltAt (termCast (Rew.emb (v 0))) Y ⋏
            Jat (termCast (Rew.emb (v 0))) (termCast (Rew.emb (v 1))))) = _
          rw [embK_neg, embK_and, embK_ltAt, embK_Jat, LogicalConnective.HomClass.map_neg,
            LogicalConnective.HomClass.map_and, rew_ltW, rew_jlevAt, hY]
          congr 1
          show ltW _ _ ⋏ jlevAt ⊤ _ _ = ltW _ _ ⋏ jlevAt ⊤ _ _
          rw [show embT (termCast (Rew.emb (v 0)) : Semiterm LXJ ℕ n) =
              Semiterm.lMap embedW (termCast (Rew.emb (v 0))) from rfl,
            show embT (termCast (Rew.emb (v 1)) : Semiterm LXJ ℕ n) =
              Semiterm.lMap embedW (termCast (Rew.emb (v 1))) from rfl,
            ← emb_lMap_term k g, ← emb_lMap_term k g]
        rw [e1, e2]
        exact Cong.atom (hNQ _ _ hj ha)

end Producer

/-! ### The embedded instance and the two producers -/

section Corollaries

/-- **The embedded finitary instance** `A_{k̄}(t)`: `AAt F #1 (emb A)` (the body of `closureAxJ A`
for `F = Jat #1 #0`, of `indAxJ A F` in general) translated by `embK` (`J ↦ Jlev ⊤`, `X` empty),
at `y := k̄`, `x := t` (`/[t, k̄]`: `#0 = x`, `#1 = y`). -/
def embInst (F : Semiformula LXJ ℕ 2) (k : ℕ) (A : FormJ) (t : SyntacticTerm LIinfW) :
    Proposition LIinfW :=
  (embK (AAt F (#1 : Semiterm LXJ ℕ 2) (Rewriting.emb A : Semiformula LForm ℕ 2)))/[t, numI k]

/-- **The producer, general form** (any bound `g`, any own-place formula `F`, any `Ok` with the four
atom pairs): `unfoldW A k g t` and `embInst F k A t` are `Cong`ruent, with index `cdepth A`. -/
theorem cong_unfold {Ok : Proposition LIinfW → Proposition LIinfW → Prop} (k : ℕ)
    (g : StageAt k) (F : Semiformula LXJ ℕ 2)
    (hAr : ∀ B, IsArithLit B → Ok B B)
    (hP : ∀ s : SyntacticTerm LIinfW, s.freeVariables = ∅ →
      Ok (stageAt ⟨k, g⟩ s) ((embK F)/[s, numI k]))
    (hQ : ∀ j a : SyntacticTerm LIinfW, j.freeVariables = ∅ → a.freeVariables = ∅ →
      Ok (jlevAt (k : WithTop ℕ) j a) (qTop k j a))
    (hNQ : ∀ j a : SyntacticTerm LIinfW, j.freeVariables = ∅ → a.freeVariables = ∅ →
      Ok (njlevAt (k : WithTop ℕ) j a) (∼(qTop k j a)))
    {A : FormJ} (hA : PositiveP A) {t : SyntacticTerm LIinfW} (ht : t.freeVariables = ∅) :
    Cong Ok (cdepth A) (unfoldW A k g t) (embInst F k A t) := by
  have hρ : ∀ i : Fin 2, (![t, numI k] i).freeVariables = ∅ := by
    intro i
    fin_cases i
    · exact ht
    · exact numI_freeVariables k
  exact cong_AAt k g F hAr hP hQ hNQ A hA ![t, numI k] hρ (#1) rfl

/-- `J(#1,#0)` embedded and instantiated: `(embK (J y x))/[s, t] = Jlev ⊤ (t, s)`. -/
theorem embK_Jat_inst (s t : SyntacticTerm LIinfW) :
    (embK (Jat #1 #0 : Semiformula LXJ ℕ 2))/[s, t] = jlevAt ⊤ t s := by
  rw [embK_Jat]
  show Rew.subst ![s, t] ▹ jlevAt ⊤ (embT #1) (embT #0) = _
  rw [rew_jlevAt]
  rfl

/-- **The forward producer.**  For a positive form `A` and a closed `t`, the unfolding at level `k`
(`P ↦ I_k`, `Q ↦ Jlev k`) is `OkFwd k`-congruent to the embedded finitary instance
(`P ↦ Jlev ⊤ (k̄,·)`, `Q ↦ a < k̄ ∧ Jlev ⊤ (a,·)`); index `cdepth A`. -/
theorem cong_unfold_fwd (k : ℕ) {A : FormJ} (hA : PositiveP A) {t : SyntacticTerm LIinfW}
    (ht : t.freeVariables = ∅) :
    Cong (OkFwd k) (cdepth A) (unfoldW A k (StageAt.top k) t)
      (embInst (Jat #1 #0) k A t) :=
  cong_unfold k (StageAt.top k) (Jat #1 #0)
    (fun _ h => Or.inl ⟨h, rfl⟩)
    (fun s hs => Or.inr (Or.inl ⟨s, hs, rfl, embK_Jat_inst s (numI k)⟩))
    (fun j a hj ha => Or.inr (Or.inr (Or.inl ⟨j, a, hj, ha, rfl, rfl⟩)))
    (fun j a hj ha => Or.inr (Or.inr (Or.inr ⟨j, a, hj, ha, rfl, rfl⟩)))
    hA ht

/-- **The backward producer**: the embedded finitary instance is `OkBwd k`-congruent to the unfolding
at level `k`. -/
theorem cong_unfold_bwd (k : ℕ) {A : FormJ} (hA : PositiveP A) {t : SyntacticTerm LIinfW}
    (ht : t.freeVariables = ∅) :
    Cong (OkBwd k) (cdepth A) (embInst (Jat #1 #0) k A t)
      (unfoldW A k (StageAt.top k) t) :=
  cong_bwd_of_fwd (cong_unfold_fwd k hA ht)

/-! #### The closure axiom: the embedded instance in the shape the replay consumes -/

theorem embInst_closure (k : ℕ) (A : FormJ) (t : SyntacticTerm LIinfW) :
    embInst (Jat #1 #0) k A t =
      (Rewriting.emb (embK (AAt (ξ := Empty) (Jat #1 #0) (#1 : Semiterm LXJ Empty 2) A)) :
        Semiformula LIinfW ℕ 2)/[t, numI k] := by
  unfold embInst
  rw [← embK_emb, ← AAt_emb]
  rfl

/-- **`Rewriting.emb (embK (closureAxJ A))` at `y := k̄`, `x := t`.**  The axiom is `∀y ∀x (B → J(y,x))`
with `B = emb (embK (AAt (Jat #1 #0) #1 A))`; instantiating the two universal quantifiers at the numerals
`k`, `t` (`Cong.all`'s `φ/[numI m]`, then `/[t]`) gives `embInst (Jat #1 #0) k A t 🡒 Jlev ⊤ (k̄, t)`. -/
theorem closure_axiom_inst (A : FormJ) (k : ℕ) (t : SyntacticTerm LIinfW) :
    ∃ φ₁ : Semiproposition LIinfW 1,
      (Rewriting.emb (embK (closureAxJ A)) : Proposition LIinfW) = ∀¹ φ₁ ∧
      ∃ φ₂ : Semiproposition LIinfW 1, φ₁/[numI k] = ∀¹ φ₂ ∧
        φ₂/[t] = (embInst (Jat #1 #0) k A t 🡒 jlevAt ⊤ (numI k) t) := by
  set X : Semiformula LIinfW ℕ 2 :=
    (Rewriting.emb (embK (AAt (ξ := Empty) (Jat #1 #0) (#1 : Semiterm LXJ Empty 2) A)) :
      Semiformula LIinfW ℕ 2) with hX
  refine ⟨∀¹ (X 🡒 jlevAt ⊤ #1 #0), ?_, (Rew.subst ![numI k]).q ▹ (X 🡒 jlevAt ⊤ #1 #0), ?_, ?_⟩
  · have hJ : (Rewriting.emb (jlevAt ⊤ (embT (#1 : Semiterm LXJ Empty 2)) (embT #0)) :
        Semiformula LIinfW ℕ 2) = jlevAt ⊤ #1 #0 := rew_jlevAt Rew.emb ⊤ _ _
    rw [closureAxJ, embK_all, embK_all, embK_imp, embK_Jat, emb_all', emb_all',
      LogicalConnective.HomClass.map_imply, hJ]
  · exact Rewriting.app_all _ _
  · rw [subst_q_inst, embInst_closure, LogicalConnective.HomClass.map_imply, rew_jlevAt]
    rfl

end Corollaries

/-! ### The producer composed with T5: the consumer-ready derivations -/

section Derive

variable {Ad : FormJ} {H : Set ThetaVNoteD → Set ThetaVNoteD}

theorem params_embInst (F : Semiformula LXJ ℕ 2) (k : ℕ) (A : FormJ) (t : SyntacticTerm LIinfW) :
    params (embInst F k A t) = ∅ :=
  (params_rew _ _).trans (params_embK _)

theorem image_params_unfoldW_top (hH : ThetaVNoteD.NiceS H) (k : ℕ) (A : FormJ)
    (t : SyntacticTerm LIinfW) : Stage.val '' params (unfoldW A k (StageAt.top k) t) ⊆ H ∅ :=
  (Set.image_mono (params_unfoldW A k (StageAt.top k) t)).trans (by
    rw [Set.image_singleton]
    exact Set.singleton_subset_iff.mpr (hH.Omega_mem k))

theorem image_params_embInst (F : Semiformula LXJ ℕ 2) (k : ℕ) (A : FormJ)
    (t : SyntacticTerm LIinfW) : Stage.val '' params (embInst F k A t) ⊆ H ∅ := by
  rw [params_embInst, Set.image_empty]
  exact Set.empty_subset _

/-- **`⊢ ¬A_k(t; I_k, Jlev k), A_{k̄}(t)`**: the unfolding at level `k` implies the embedded finitary
instance, at height `Ω_{k+1} ⊕ (4 + 2 · cdepth A)`, cut rank `0`, in every nice `H`. -/
theorem transfer_unfold_fwd (hH : ThetaVNoteD.NiceS H) (k : ℕ) {A : FormJ} (hA : PositiveP A)
    {t : SyntacticTerm LIinfW} (ht : t.freeVariables = ∅) {Γ : Sequent LIinfW}
    (hΓ : paramsVal Γ ⊆ H ∅) :
    IDwDerivable Ad ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat (4 + 2 * cdepth A)))
      (∼(unfoldW A k (StageAt.top k) t) :: embInst (Jat #1 #0) k A t :: Γ) :=
  transfer5_fwd hH k hΓ (cong_unfold_fwd k hA ht) (image_params_unfoldW_top hH k A t)
    (image_params_embInst _ k A t)

/-- **`⊢ ¬A_{k̄}(t), A_k(t; I_k, Jlev k)`**: the embedded finitary instance implies the unfolding at
level `k`, at height `Ω_{k+1} ⊕ (4 + 2 · cdepth A)`, cut rank `0`, in every nice `H`. -/
theorem transfer_unfold_bwd (hH : ThetaVNoteD.NiceS H) (k : ℕ) {A : FormJ} (hA : PositiveP A)
    {t : SyntacticTerm LIinfW} (ht : t.freeVariables = ∅) {Γ : Sequent LIinfW}
    (hΓ : paramsVal Γ ⊆ H ∅) :
    IDwDerivable Ad ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat (4 + 2 * cdepth A)))
      (∼(embInst (Jat #1 #0) k A t) :: unfoldW A k (StageAt.top k) t :: Γ) :=
  transfer5_bwd hH k hΓ (cong_unfold_bwd k hA ht) (image_params_embInst _ k A t)
    (image_params_unfoldW_top hH k A t)

end Derive

/-! ### Smoke tests: `A := P(x)` and `A := Q(x, y)` -/

section Smoke

/-- `A := P(x)`: the unfolding is `I_k t`. -/
theorem smoke_unfold_P (k : ℕ) (t : SyntacticTerm LIinfW) :
    unfoldW (Pat (#0 : Semiterm LForm Empty 2)) k (StageAt.top k) t = IOmegaAt k t := by
  show Semiformula.rel (Sum.inr (IInfRelW.stage ⟨k, StageAt.top k⟩))
    (fun i => Rew.subst ![t, numI k] (Rew.emb (Semiterm.lMap (formHomAt k (StageAt.top k))
      (![(#0 : Semiterm LForm Empty 2)] i)))) = _
  congr 1
  funext i
  obtain rfl := Subsingleton.elim i 0
  rfl

/-- `A := P(x)`: the embedded instance is `Jlev ⊤ (k̄, t)`. -/
theorem smoke_emb_P (k : ℕ) (t : SyntacticTerm LIinfW) :
    embInst (Jat #1 #0) k (Pat (#0 : Semiterm LForm Empty 2)) t = jlevAt ⊤ (numI k) t := by
  have h : (embK (AAt (ξ := ℕ) (Jat #1 #0) (#1 : Semiterm LXJ ℕ 2)
      (Rewriting.emb (Pat (#0 : Semiterm LForm Empty 2)) : Semiformula LForm ℕ 2))) =
      embK (Jat #1 #0) := by
    show embK ((Jat #1 #0 : Semiformula LXJ ℕ 2)/[#0, #1]) = _
    congr 1
    show Rew.subst ![#0, #1] ▹ (Jat #1 #0 : Semiformula LXJ ℕ 2) = _
    refine (Semiformula.rew_rel2 _).trans ?_
    rfl
  unfold embInst
  rw [h]
  exact embK_Jat_inst t (numI k)

/-- `A := P(x)`: the congruence is one `OkFwd` atom pair (`I_k t ~ Jlev ⊤ (k̄, t)`), index `0`. -/
example (k : ℕ) {t : SyntacticTerm LIinfW} (ht : t.freeVariables = ∅) :
    Cong (OkFwd k) 0 (IOmegaAt k t) (jlevAt ⊤ (numI k) t) := by
  have h := cong_unfold_fwd k (A := Pat (#0 : Semiterm LForm Empty 2)) (positiveP_Pat _) ht
  rwa [smoke_unfold_P, smoke_emb_P] at h

/-- `A := Q(x, y)`: the unfolding is `Jlev k (t, k̄)`. -/
theorem smoke_unfold_Q (k : ℕ) (t : SyntacticTerm LIinfW) :
    unfoldW (Qat (#0 : Semiterm LForm Empty 2) #1) k (StageAt.top k) t =
      jlevAt (k : WithTop ℕ) t (numI k) := by
  show Semiformula.rel (Sum.inr (IInfRelW.jlev (k : WithTop ℕ)))
    (fun i => Rew.subst ![t, numI k] (Rew.emb (Semiterm.lMap (formHomAt k (StageAt.top k))
      (![(#0 : Semiterm LForm Empty 2), #1] i)))) = _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- `A := Q(x, y)`: the embedded instance is `t < k̄ ∧ Jlev ⊤ (t, k̄)`. -/
theorem smoke_emb_Q (k : ℕ) (t : SyntacticTerm LIinfW) :
    embInst (Jat #1 #0) k (Qat (#0 : Semiterm LForm Empty 2) #1) t = qTop k t (numI k) := by
  unfold embInst
  show Rew.subst ![t, numI k] ▹ embK (ltAt (#0 : Semiterm LXJ ℕ 2) #1 ⋏ Jat #0 #1) = _
  rw [embK_and, embK_ltAt, embK_Jat, LogicalConnective.HomClass.map_and, rew_ltW, rew_jlevAt]
  rfl

/-- `A := Q(x, y)`: the congruence is one `OkFwd` atom pair, index `0`. -/
example (k : ℕ) {t : SyntacticTerm LIinfW} (ht : t.freeVariables = ∅) :
    Cong (OkFwd k) 0 (jlevAt (k : WithTop ℕ) t (numI k)) (qTop k t (numI k)) := by
  have h := cong_unfold_fwd k (A := Qat (#0 : Semiterm LForm Empty 2) #1) (positiveP_Qat _ _) ht
  rwa [smoke_unfold_Q, smoke_emb_Q] at h

/-- A quantifier: `A := ∀z (Q(z, y) ∨ P(x))`, index `cdepth = (max 0 0 + 1) + 1 = 2`. -/
example (k : ℕ) {t : SyntacticTerm LIinfW} (ht : t.freeVariables = ∅) :
    Cong (OkFwd k) 2
      (unfoldW (∀¹ (Qat (#0 : Semiterm LForm Empty 3) #2 ⋎ Pat #1) : FormJ) k (StageAt.top k) t)
      (embInst (Jat #1 #0) k (∀¹ (Qat (#0 : Semiterm LForm Empty 3) #2 ⋎ Pat #1) : FormJ) t) := by
  have h := cong_unfold_fwd k (A := (∀¹ (Qat (#0 : Semiterm LForm Empty 3) #2 ⋎ Pat #1) : FormJ))
    ((positiveP_all _).mpr ((positiveP_or _ _).mpr ⟨positiveP_Qat _ _, positiveP_Pat _⟩)) ht
  have hc : cdepth (∀¹ (Qat (#0 : Semiterm LForm Empty 3) #2 ⋎ Pat #1) : FormJ) = 2 := by
    simp [cdepth, Qat, Pat]
  rwa [hc] at h

end Smoke

end Transfer

end IDw

end OrdinalAnalysis
