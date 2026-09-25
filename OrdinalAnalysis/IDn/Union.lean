/-
  The embeddings between the languages of finitely many levels, the model-expansion
  lemma, and `IDlt`, the union of `ID A` over all finite levels.

  **The embeddings.** `mapHom f : LXIN ι →ᵥ LXIN ι'`, for any `f : ι → ι'`, fixes
  arithmetic and `X` and sends `I_k ↦ I_(f k)`. `embedSucc n := mapHom Fin.castSucc :
  LXIn n →ᵥ LXIn (n+1)` and `embedOmega n := mapHom Fin.val : LXIn n →ᵥ LXIomega` are the
  two embeddings used here; `Semiformula.lMap` along either is "formula
  translation along the embedding" (`lMap_Iat`, `lMap_Xat`, `lMap_closureAxAt`,
  `mapHom_comp`). The corresponding facts for `substIAt`/`opAt`/`indAxAt` (needed to push
  a *family* `A : Fin n → Semisentence (LXIn n) 1` up into `LXIomega` termwise) are not
  built here — see the scope note on `provable_IDlt_iff`.

  **The model-expansion lemma.** `expandStruc n N E`, for an `LXIn n`-structure `N` and an
  arbitrary reading `E : ℕ → Set M` of *every* level, is the `LXIomega`-structure that
  copies `N` at every level `< n` and uses `E` at every level `≥ n`. `eval_expandStruc`
  shows it agrees with `N` on every translated `LXIn n`-formula, for *any* `E` — this is
  the "a model of `ID n A` expands to the language `LXIω` interpreting new
  predicates arbitrarily" fact (`models_expand`).

  **`IDlt`.** Directly, `IDlt A := ID A` at `ι := ℕ` (`Sound.lean`'s soundness already
  covers `ι := ℕ`, since `ℕ` is a linear, well-founded order, so `IDlt_consistent` is
  immediate from `ID_consistent`; this is the same deliberate deviation from proving it
  via `compact_cumulative` — the
  syntactic route is used instead, both here and for `provable_IDlt_iff`). To see `IDlt`
  as a genuine union, `IDseq m := paLXIN ℕ ∪ ⋃ k < m, idAxiomsAt k (A k)` is a
  cumulative (`Cumulative_IDseq`) family of theories, all already living in `LXIω` (no
  embedding needed for *this* direction, since `IDlt`'s own closure/induction axioms are
  already indexed by `k : ℕ`, i.e. already "at every finite level" by construction), with
  `IDlt_eq_iUnion : IDlt A = ⋃ m, IDseq m`. `provable_IDlt_iff` then follows from
  `Entailment.Compact (Theory L)` (every proof uses finitely many axioms) and
  `Cumulative.finset_mem` (a finite set of axioms already sits inside one `IDseq m`).

  Contents.

    `mapHom`, `embedSucc`, `embedOmega`                    the embeddings
    `lMap_Iat`, `lMap_Xat`, `lMap_closureAxAt`              formula translation along them
    `termMapHom_comp`, `relMapHom_comp`, `mapHom_comp`, `lMap_embedSucc_embedOmega`
    `expandStruc`, `eval_expandStruc`, `models_expand`      **the expansion lemma**
    `IDlt`, `IDseq`, `cumulative_IDseq`, `IDlt_eq_iUnion`
    `IDlt_consistent`                                       **consistency**
    `IDseq_subset_IDlt`, `provable_IDlt_iff`                **the union/expansion theorem**
-/
import OrdinalAnalysis.IDn.Sound

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### The embeddings -/

/-- The relation-symbol map of `mapHom f`: fix arithmetic and `X`, send `I_k` to
`I_(f k)`. -/
def relMapN {ι ι' : Type} (f : ι → ι') : {k : ℕ} → (LXIN ι).Rel k → (LXIN ι').Rel k
  | _, Sum.inl r => Sum.inl r
  | _, Sum.inr IXRelN.X => Sum.inr IXRelN.X
  | _, Sum.inr (IXRelN.I j) => Sum.inr (IXRelN.I (f j))

/-- The function-symbol map: `IXLangN` has no function symbols, so this is just the
identity on the arithmetic part. -/
def funcMapN {ι ι' : Type} : {k : ℕ} → (LXIN ι).Func k → (LXIN ι').Func k
  | _, Sum.inl f => Sum.inl f
  | _, Sum.inr f => PEmpty.elim f

/-- **`I_k ↦ I_(f k)`, as a homomorphism of languages**, for any `f : ι → ι'`. -/
def mapHom {ι ι' : Type} (f : ι → ι') : LXIN ι →ᵥ LXIN ι' := ⟨funcMapN, relMapN f⟩

section MapHomAtoms

variable {ι ι' : Type} (f : ι → ι')

@[simp] theorem mapHom_rel_inl {k : ℕ} (r : (ℒₒᵣ : Language).Rel k) :
    (mapHom f).rel (Sum.inl r) = Sum.inl r := rfl

@[simp] theorem mapHom_rel_X : (mapHom f).rel (Sum.inr IXRelN.X) = Sum.inr IXRelN.X := rfl

@[simp] theorem mapHom_rel_I (j : ι) :
    (mapHom f).rel (Sum.inr (IXRelN.I j)) = Sum.inr (IXRelN.I (f j)) := rfl

@[simp] theorem mapHom_func_inl {k : ℕ} (g : (ℒₒᵣ : Language).Func k) :
    (mapHom f).func (Sum.inl g) = Sum.inl g := rfl

end MapHomAtoms

/-- **The embedding of `LXIn n` into `LXIn (n+1)`.** -/
def embedSucc (n : ℕ) : LXIn n →ᵥ LXIn (n + 1) := mapHom Fin.castSucc

/-- **The embedding of `LXIn n` into `LXIomega`.** -/
def embedOmega (n : ℕ) : LXIn n →ᵥ LXIomega := mapHom Fin.val

section MapHom

variable {ι ι' : Type} (f : ι → ι')

/-- **Unfolding `lMap` on an atom, at any arity.** Kept separate from
`Semiformula.lMap_rel` because rewriting with the latter across two different instances
of `LXIN` hits a transparency wall (`(LXIN ι).Rel k` needs to unfold through
`Language.add`, a plain `def`, to be seen as the sum type `rw`'s congruence-building
expects); stating it as its own `rfl` lemma, checked at full transparency during
elaboration, does not have this problem. -/
theorem lMap_relK {ξ : Type*} {n k : ℕ} (r : (LXIN ι).Rel k)
    (v : Fin k → Semiterm (LXIN ι) ξ n) :
    Semiformula.lMap (mapHom f) (Semiformula.rel r v) =
      Semiformula.rel ((mapHom f).rel r) (fun i => Semiterm.lMap (mapHom f) (v i)) := rfl

theorem lMap_nrelK {ξ : Type*} {n k : ℕ} (r : (LXIN ι).Rel k)
    (v : Fin k → Semiterm (LXIN ι) ξ n) :
    Semiformula.lMap (mapHom f) (Semiformula.nrel r v) =
      Semiformula.nrel ((mapHom f).rel r) (fun i => Semiterm.lMap (mapHom f) (v i)) := rfl

/-- Every atom `I_k(t)` translates to `I_(f k)(t)`. -/
theorem lMap_Iat {ξ : Type*} {n : ℕ} (k : ι) (t : Semiterm (LXIN ι) ξ n) :
    Semiformula.lMap (mapHom f) (Iat k t) = Iat (f k) (Semiterm.lMap (mapHom f) t) := by
  have e1 : Semiformula.lMap (mapHom f) (Iat k t) =
      Semiformula.rel (Sum.inr (IXRelN.I (f k)) : (LXIN ι').Rel 1)
        (Semiterm.lMap (mapHom f) ∘ ![t]) := rfl
  rw [e1, Matrix.comp₁]; rfl

theorem lMap_Xat {ξ : Type*} {n : ℕ} (t : Semiterm (LXIN ι) ξ n) :
    Semiformula.lMap (mapHom f) (Xat t) = Xat (Semiterm.lMap (mapHom f) t) := by
  have e1 : Semiformula.lMap (mapHom f) (Xat t) =
      Semiformula.rel (Sum.inr IXRelN.X : (LXIN ι').Rel 1)
        (Semiterm.lMap (mapHom f) ∘ ![t]) := rfl
  rw [e1, Matrix.comp₁]; rfl

/-- **Translating the closure axiom of level `k`**: `mapHom f` sends `closureAxAt k A` to
`closureAxAt (f k) (lMap A)`, for any `f` (no injectivity needed — the closure axiom does
not branch on the level index). -/
theorem lMap_closureAxAt (k : ι) (A : Semisentence (LXIN ι) 1) :
    Semiformula.lMap (mapHom f) (closureAxAt k A) =
      closureAxAt (f k) (Semiformula.lMap (mapHom f) A) := by
  simp only [closureAxAt, Semiformula.lMap_all, LogicalConnective.HomClass.map_imply, lMap_Iat,
    Semiterm.lMap_bvar]

end MapHom

/-- Term translation composes. -/
theorem termMapHom_comp {ι ι' ι'' : Type} (g : ι' → ι'') (f : ι → ι') {ξ : Type*} {n : ℕ} :
    ∀ (t : Semiterm (LXIN ι) ξ n),
      Semiterm.lMap (mapHom g) (Semiterm.lMap (mapHom f) t) = Semiterm.lMap (mapHom (g ∘ f)) t
  | .bvar x => rfl
  | .fvar x => rfl
  | .func h w => by
      have e1 : Semiterm.lMap (mapHom g) (Semiterm.lMap (mapHom f) (Semiterm.func h w)) =
          Semiterm.func ((mapHom g).func ((mapHom f).func h))
            (fun i => Semiterm.lMap (mapHom g) (Semiterm.lMap (mapHom f) (w i))) := rfl
      have e2 : Semiterm.lMap (mapHom (g ∘ f)) (Semiterm.func h w) =
          Semiterm.func ((mapHom (g ∘ f)).func h) (fun i => Semiterm.lMap (mapHom (g ∘ f)) (w i)) :=
        rfl
      rw [e1, e2]
      rcases h with h | h
      · congr 1
        funext i
        exact termMapHom_comp g f (w i)
      · exact h.elim

/-- Relation-symbol translation composes. -/
theorem relMapHom_comp {ι ι' ι'' : Type} (g : ι' → ι'') (f : ι → ι') {k : ℕ}
    (r : (LXIN ι).Rel k) :
    (mapHom g).rel ((mapHom f).rel r) = (mapHom (g ∘ f)).rel r := by
  rcases r with r | r
  · rfl
  · cases r with
    | X => rfl
    | I j => rfl

/-- **Composing two `mapHom`'s is `mapHom` of the composite.** -/
theorem mapHom_comp {ι ι' ι'' : Type} (g : ι' → ι'') (f : ι → ι') :
    ∀ {ξ : Type*} {n : ℕ} (φ : Semiformula (LXIN ι) ξ n),
      Semiformula.lMap (mapHom g) (Semiformula.lMap (mapHom f) φ) =
        Semiformula.lMap (mapHom (g ∘ f)) φ := by
  intro ξ n φ
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
      have e1 : Semiformula.lMap (mapHom g) (Semiformula.lMap (mapHom f) (Semiformula.rel r v)) =
          Semiformula.rel ((mapHom g).rel ((mapHom f).rel r))
            (fun i => Semiterm.lMap (mapHom g) (Semiterm.lMap (mapHom f) (v i))) := rfl
      have e2 : Semiformula.lMap (mapHom (g ∘ f)) (Semiformula.rel r v) =
          Semiformula.rel ((mapHom (g ∘ f)).rel r) (fun i => Semiterm.lMap (mapHom (g ∘ f)) (v i)) :=
        rfl
      rw [e1, e2, relMapHom_comp]
      congr 1
      funext i
      exact termMapHom_comp g f (v i)
  | hnrel r v =>
      have e1 : Semiformula.lMap (mapHom g) (Semiformula.lMap (mapHom f) (Semiformula.nrel r v)) =
          Semiformula.nrel ((mapHom g).rel ((mapHom f).rel r))
            (fun i => Semiterm.lMap (mapHom g) (Semiterm.lMap (mapHom f) (v i))) := rfl
      have e2 : Semiformula.lMap (mapHom (g ∘ f)) (Semiformula.nrel r v) =
          Semiformula.nrel ((mapHom (g ∘ f)).rel r)
            (fun i => Semiterm.lMap (mapHom (g ∘ f)) (v i)) := rfl
      rw [e1, e2, relMapHom_comp]
      congr 1
      funext i
      exact termMapHom_comp g f (v i)
  | hand φ ψ ihφ ihψ =>
      simp only [LogicalConnective.HomClass.map_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
      simp only [LogicalConnective.HomClass.map_or, ihφ, ihψ]
  | hall φ ih =>
      simp only [Semiformula.lMap_all, ih]
  | hexs φ ih =>
      simp only [Semiformula.lMap_exs, ih]

/-- **The two embeddings of `LXIn n` into `LXIomega` agree**: going via `LXIn (n+1)` or
directly gives the same translation, since `Fin.val ∘ Fin.castSucc = Fin.val`. -/
theorem lMap_embedSucc_embedOmega (n : ℕ) {ξ : Type*} {m : ℕ} (φ : Semiformula (LXIn n) ξ m) :
    Semiformula.lMap (embedOmega (n + 1)) (Semiformula.lMap (embedSucc n) φ) =
      Semiformula.lMap (embedOmega n) φ := by
  have hcomp : (Fin.val : Fin (n + 1) → ℕ) ∘ (Fin.castSucc : Fin n → Fin (n + 1)) = Fin.val := by
    funext j; exact Fin.val_castSucc j
  rw [embedOmega, embedSucc, embedOmega, mapHom_comp, hcomp]

/-! ### The model-expansion lemma -/

section Expand

variable {M : Type*} (n : ℕ) (N : Structure (LXIn n) M) (E : ℕ → Set M)

/-- The fresh predicates of the expanded structure: copy `N` below `n`, use `E` at and
above `n`. -/
@[instance_reducible] def expandIx : Structure (IXLangN ℕ) M where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ r v => match r with
    | IXRelN.X => N.rel (Sum.inr IXRelN.X) v
    | IXRelN.I j => if h : j < n then N.rel (Sum.inr (IXRelN.I ⟨j, h⟩)) v else v 0 ∈ E j

/-- **The expanded `LXIomega`-structure**: arithmetic exactly as in `N`, `X` and the
levels `< n` exactly as in `N`, the levels `≥ n` read by `E`. -/
@[instance_reducible] def expandStruc : Structure LXIomega M :=
  Structure.add ℒₒᵣ (IXLangN ℕ) M (str₁ := N.lMap (toLXIN (Fin n))) (str₂ := expandIx n N E)

/-- **Term values translate correctly into the expansion**: a term of `N` evaluates the
same way after translation into the expanded structure, for any reading `E`. -/
theorem val_expandStruc {ξ : Type*} {m : ℕ} (e : Fin m → M) (f : ξ → M) :
    ∀ (t : Semiterm (LXIn n) ξ m),
      Semiterm.val (s := expandStruc n N E) e f (Semiterm.lMap (embedOmega n) t) =
        Semiterm.val (s := N) e f t
  | .bvar x => rfl
  | .fvar x => rfl
  | .func g w => by
      have e1 : Semiterm.val (s := expandStruc n N E) e f
          (Semiterm.lMap (embedOmega n) (Semiterm.func g w)) =
          (expandStruc n N E).func ((embedOmega n).func g)
            (fun i => Semiterm.val (s := expandStruc n N E) e f
              (Semiterm.lMap (embedOmega n) (w i))) := rfl
      rw [e1]
      rcases g with g | g
      · have e2 : ((embedOmega n).func (Sum.inl g) : LXIomega.Func _) = Sum.inl g := rfl
        have e3 : (expandStruc n N E).func (Sum.inl g)
            (fun i => Semiterm.val (s := expandStruc n N E) e f
              (Semiterm.lMap (embedOmega n) (w i))) =
            N.func (Sum.inl g)
              (fun i => Semiterm.val (s := expandStruc n N E) e f
                (Semiterm.lMap (embedOmega n) (w i))) := rfl
        rw [e2, e3]
        have e4 : N.func (Sum.inl g) (fun i => Semiterm.val (s := N) e f (w i)) =
            Semiterm.val (s := N) e f (Semiterm.func (Sum.inl g) w) := rfl
        rw [← e4]
        congr 1
        funext i
        exact val_expandStruc e f (w i)
      · exact g.elim

/-- **Every translated `LXIn n`-formula has the same truth value in `N` and in the
expansion**, for any reading `E` of the new levels — the model literally does not see
`E`. -/
theorem eval_expandStruc {ξ : Type*} {m : ℕ} (e : Fin m → M) (f : ξ → M) :
    ∀ (φ : Semiformula (LXIn n) ξ m),
      Semiformula.Eval (s := expandStruc n N E) e f (Semiformula.lMap (embedOmega n) φ) ↔
        Semiformula.Eval (s := N) e f φ := by
  intro φ
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v =>
      have hv : (fun i => Semiterm.val (s := expandStruc n N E) e f
          (Semiterm.lMap (embedOmega n) (v i))) = fun i => Semiterm.val (s := N) e f (v i) := by
        funext i; exact val_expandStruc n N E e f (v i)
      rcases r with r | r
      · have e1 : Semiformula.Eval (s := expandStruc n N E) e f
            (Semiformula.lMap (embedOmega n) (Semiformula.rel (Sum.inl r) v)) =
            N.rel (Sum.inl r) (fun i => Semiterm.val (s := expandStruc n N E) e f
              (Semiterm.lMap (embedOmega n) (v i))) := rfl
        rw [e1, hv]; exact Iff.rfl
      · cases r with
        | X =>
            have e1 : Semiformula.Eval (s := expandStruc n N E) e f
                (Semiformula.lMap (embedOmega n) (Semiformula.rel (Sum.inr IXRelN.X) v)) =
                N.rel (Sum.inr IXRelN.X) (fun i => Semiterm.val (s := expandStruc n N E) e f
                  (Semiterm.lMap (embedOmega n) (v i))) := rfl
            rw [e1, hv]; exact Iff.rfl
        | I j =>
            have e1 : Semiformula.Eval (s := expandStruc n N E) e f
                (Semiformula.lMap (embedOmega n) (Semiformula.rel (Sum.inr (IXRelN.I j)) v)) =
                (if h : (j : ℕ) < n then N.rel (Sum.inr (IXRelN.I ⟨(j : ℕ), h⟩))
                    (fun i => Semiterm.val (s := expandStruc n N E) e f
                      (Semiterm.lMap (embedOmega n) (v i)))
                  else (fun i => Semiterm.val (s := expandStruc n N E) e f
                      (Semiterm.lMap (embedOmega n) (v i))) 0 ∈ E (j : ℕ)) := rfl
            rw [e1, dif_pos j.isLt, hv]
            have hj : (⟨(j : ℕ), j.isLt⟩ : Fin n) = j := Fin.eta j j.isLt
            rw [hj]
            exact Iff.rfl
  | hnrel r v =>
      have hv : (fun i => Semiterm.val (s := expandStruc n N E) e f
          (Semiterm.lMap (embedOmega n) (v i))) = fun i => Semiterm.val (s := N) e f (v i) := by
        funext i; exact val_expandStruc n N E e f (v i)
      rcases r with r | r
      · have e1 : Semiformula.Eval (s := expandStruc n N E) e f
            (Semiformula.lMap (embedOmega n) (Semiformula.nrel (Sum.inl r) v)) =
            ¬N.rel (Sum.inl r) (fun i => Semiterm.val (s := expandStruc n N E) e f
              (Semiterm.lMap (embedOmega n) (v i))) := rfl
        rw [e1, hv]; exact Iff.rfl
      · cases r with
        | X =>
            have e1 : Semiformula.Eval (s := expandStruc n N E) e f
                (Semiformula.lMap (embedOmega n) (Semiformula.nrel (Sum.inr IXRelN.X) v)) =
                ¬N.rel (Sum.inr IXRelN.X) (fun i => Semiterm.val (s := expandStruc n N E) e f
                  (Semiterm.lMap (embedOmega n) (v i))) := rfl
            rw [e1, hv]; exact Iff.rfl
        | I j =>
            have e1 : Semiformula.Eval (s := expandStruc n N E) e f
                (Semiformula.lMap (embedOmega n) (Semiformula.nrel (Sum.inr (IXRelN.I j)) v)) =
                ¬(if h : (j : ℕ) < n then N.rel (Sum.inr (IXRelN.I ⟨(j : ℕ), h⟩))
                    (fun i => Semiterm.val (s := expandStruc n N E) e f
                      (Semiterm.lMap (embedOmega n) (v i)))
                  else (fun i => Semiterm.val (s := expandStruc n N E) e f
                      (Semiterm.lMap (embedOmega n) (v i))) 0 ∈ E (j : ℕ)) := rfl
            rw [e1, dif_pos j.isLt, hv]
            have hj : (⟨(j : ℕ), j.isLt⟩ : Fin n) = j := Fin.eta j j.isLt
            rw [hj]
            exact Iff.rfl
  | hand φ ψ ihφ ihψ =>
      rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
      exact and_congr (ihφ e) (ihψ e)
  | hor φ ψ ihφ ihψ =>
      rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
      exact or_congr (ihφ e) (ihψ e)
  | hall φ ih =>
      rw [Semiformula.lMap_all, Semiformula.eval_all, Semiformula.eval_all]
      exact forall_congr' fun x => ih (x :> e)
  | hexs φ ih =>
      rw [Semiformula.lMap_exs, Semiformula.eval_ex, Semiformula.eval_ex]
      exact exists_congr fun x => ih (x :> e)

/-- **The model-expansion lemma**: a model of `IDn n A` expands to `LXIomega`, along
`embedOmega n`, interpreting the levels `≥ n` arbitrarily (`E`). -/
theorem models_expand [Nonempty M] (A : Fin n → Semisentence (LXIn n) 1)
    (hN : letI := N; M↓[LXIn n] ⊧* IDn n A) :
    letI := expandStruc n N E; M↓[LXIomega] ⊧* Theory.lMap (embedOmega n) (IDn n A) := by
  let _ : Structure (LXIn n) M := N
  let _ : Structure LXIomega M := expandStruc n N E
  refine Semantics.modelsSet_iff.mpr fun σ hσ => ?_
  obtain ⟨σ', hσ', rfl⟩ := hσ
  refine models_iff.mpr ?_
  refine (eval_expandStruc n N E ![] Empty.elim σ').mpr ?_
  exact models_iff.mp (Semantics.modelsSet_iff.mp hN hσ')

end Expand

/-! ### `IDlt`: the union over all finite levels -/

section IDlt

variable (A : ℕ → Semisentence LXIomega 1)

/-- **`IDlt A`**: `ID A` at `ι := ℕ`. `ℕ` is a linear, well-founded order, so
`Sound.lean`'s soundness already applies to it directly — this is what makes
`IDlt_consistent` immediate below, instead of going through `compact_cumulative` as
first planned. -/
def IDlt : Theory LXIomega := ID A

/-- **The theory of the levels `< m`**, together with full `PA`-induction for
`LXIomega`. A genuine, cumulative, finite-level piece of `IDlt A` — `IDseq m ⊆ IDseq
(m+1) ⊆ ⋯`, and every axiom of `IDlt A` sits inside some `IDseq m` (`IDlt_eq_iUnion`). -/
def IDseq (m : ℕ) : Theory LXIomega :=
  paLXIN ℕ ∪ ⋃ k, ⋃ (_ : k < m), idAxiomsAt k (A k)

theorem IDseq_subset_IDlt (m : ℕ) : IDseq A m ⊆ IDlt A := by
  rintro σ (h | h)
  · exact Or.inl h
  · refine Or.inr ?_
    simp only [Set.mem_iUnion] at h
    obtain ⟨k, -, hk⟩ := h
    exact Set.mem_iUnion_of_mem k hk

theorem IDseq_mono {m m' : ℕ} (h : m ≤ m') : IDseq A m ⊆ IDseq A m' := by
  rintro σ (h' | h')
  · exact Or.inl h'
  · refine Or.inr ?_
    simp only [Set.mem_iUnion] at h' ⊢
    obtain ⟨k, hk, hmem⟩ := h'
    exact ⟨k, lt_of_lt_of_le hk h, hmem⟩

/-- **`IDseq` is cumulative.** -/
theorem cumulative_IDseq : Cumulative (IDseq A) := fun m => IDseq_mono A (by omega)

/-- **`IDlt A` really is the union, level by level, of the finite pieces.** -/
theorem IDlt_eq_iUnion : IDlt A = ⋃ m, IDseq A m := by
  apply Set.Subset.antisymm
  · rintro σ (h | h)
    · exact Set.mem_iUnion_of_mem 0 (Or.inl h)
    · simp only [Set.mem_iUnion] at h
      obtain ⟨k, hk⟩ := h
      refine Set.mem_iUnion_of_mem (k + 1) (Or.inr ?_)
      simp only [Set.mem_iUnion]
      exact ⟨k, by omega, hk⟩
  · simp only [Set.iUnion_subset_iff]
    exact fun m => IDseq_subset_IDlt A m

/-- **`IDlt A` is consistent**, for a positive, level-bounded family `A`. Proved directly
from `Sound.lean`'s soundness at `ι := ℕ`, not via compactness (see the docstring of
`IDlt`). -/
theorem IDlt_consistent (hAp : FamilyPositive A) (hAb : FamilyLevelBounded A) :
    IDlt A ⊬ (⊥ : Sentence LXIomega) :=
  ID_consistent A hAp hAb

/-- **`provable_IDlt_iff`**: a proof of `σ` from `IDlt A` always comes from some finite
level `m` — i.e. from `IDseq A m`, `PA` plus the closure/induction axioms of every level
`< m` (the levels-`< m` part of `ID A`, in `LXIomega` directly; pushing this further down
into an honest `IDn m A'` in the smaller language `LXIn m`, for a family `A'` obtained by
downward-translating `A`, is true as well — `descend`/`SymbolsBelow`-style, along
`embedOmega m` — but is not built here: it needs a translation-of-derivations lemma this
file does not attempt. `Entailment.Compact`/`Cumulative.finset_mem` alone give the
`LXIomega`-level statement below.) -/
theorem provable_IDlt_iff (σ : Sentence LXIomega) :
    IDlt A ⊢ σ ↔ ∃ m, IDseq A m ⊢ σ := by
  constructor
  · intro h
    obtain ⟨𝓕, h𝓕sub, h𝓕fin, h𝓕⟩ := Entailment.Compact.finite_provable h
    have h𝓕fin' : 𝓕.Finite := (Set.adjunctiveSet_finite_iff 𝓕).mp h𝓕fin
    have h𝓕sub' : (𝓕 : Set (Sentence LXIomega)) ⊆ ⋃ m, IDseq A m := by
      rw [← IDlt_eq_iUnion]; exact h𝓕sub
    obtain ⟨m, hm⟩ := (cumulative_IDseq A).finset_mem (u := h𝓕fin'.toFinset)
      (by rw [Set.Finite.coe_toFinset]; exact h𝓕sub')
    refine ⟨m, ?_⟩
    have hsub : 𝓕 ⊆ IDseq A m := by rw [← Set.Finite.coe_toFinset h𝓕fin']; exact hm
    exact (Entailment.WeakerThan.ofSubset hsub).wk h𝓕
  · rintro ⟨m, hm⟩
    exact (Entailment.WeakerThan.ofSubset (IDseq_subset_IDlt A m)).wk hm

end IDlt

end IDn

end OrdinalAnalysis
